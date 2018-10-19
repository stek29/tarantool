/*
 * Copyright 2010-2018, Tarantool AUTHORS, please see AUTHORS file.
 *
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "swim.h"
#include "sio.h"
#include "uri.h"
#include "assoc.h"
#include "fiber.h"
#include "small/rlist.h"
#include "msgpuck.h"
#include "info.h"
#include <arpa/inet.h>

/**
 * Possible optimizations:
 * - track hash table versions and do not resend when a received
 *   already knows your version.
 * - on small updates send to another node only updates since a
 *   version. On rare updates it can dramatically reduce message
 *   size and its encoding time.
 */

/**
 * Global hash of all known members of the cluster. Hash key is
 * bitwise combination of ip and port, value is a struct member,
 * describing a remote instance.
 *
 * Discovered members live here until they are unavailable - in
 * such a case they are removed from the hash. But a subset of
 * members are pinned - the ones added via SWIM configuration.
 * When a member is pinned, it can not be removed from the hash,
 * and the module will ping him constantly.
 */
static struct mh_i64ptr_t *members = NULL;

static inline uint64_t
sockaddr_in_hash(const struct sockaddr_in *a)
{
	return ((uint64_t) a->sin_addr.s_addr << 16) | a->sin_port;
}

static inline void
sockaddr_in_unhash(struct sockaddr_in *a, uint64_t hash)
{
	memset(a, 0, sizeof(*a));
	a->sin_family = AF_INET;
	a->sin_addr.s_addr = hash >> 16;
	a->sin_port = hash & 0xffff;
}

enum swim_member_status {
	/**
	 * A special state visible during reconfiguration only for
	 * a newely configured members. Used actually only to
	 * correctly rollback a failed reconfiguration.
	 */
	MEMBER_NEW = 0,
	/**
	 * The instance is ok, it responds to requests, sends its
	 * members table.
	 */
	MEMBER_ALIVE,
	swim_member_status_MAX,
};

static const char *swim_member_status_strs[] = {
	"new",
	"alive",
};

/**
 * SWIM has two components: dissemination and failure detection.
 * Each in a common case independently may want to push some data
 * into the network. Dissemination sends member tables, failure
 * detection sends ping, ack, indirect ping. Event objects are
 * stored in a queue that is dispatched when output is possible,
 * as libev says, to do not block on sending.
 */
enum swim_io_event_type {
	SWIM_IO_BROADCAST_MEMBERS,
};

struct swim_io_event {
	enum swim_io_event_type type;
	struct rlist in_queue_output;
};

/**
 * A cluster member description. This structure describes the
 * last known state of an instance, that is updated periodically
 * via UDP according to SWIM protocol.
 */
struct swim_member {
	/** Instance status. */
	enum swim_member_status status;
	/** Address of the instance to which send UDP packets. */
	struct sockaddr_in addr;
	struct rlist in_queue_next;
};

/**
 * SWIM has two components: dissemination and failure detection.
 * In the original SWIM they are completely different, even sent
 * in different messages. Improved SWIM describes piggybacking of
 * some of dissemination and failure detection messages: each
 * dissemination message piggybacks a ping.
 */
enum swim_component_type {
	SWIM_DISSEMINATION = 0,
};

/** Attributes of each record of a broadcasted member table. */
enum swim_member_key {
	SWIM_MEMBER_STATUS = 0,
	SWIM_MEMBER_ADDR_HASH,
};

/**
 * SWIM message structure:
 * {
 *     SWIM_DISSEMINATION: [
 *         {
 *             SWIM_MEMBER_STATUS: uint, enum member_status,
 *             SWIM_MEMBER_ADDR_HASH: uint, (ip << 16) | port
 *         },
 *         ...
 *     ],
 * }
 */

/** SWIM dissemination MsgPack header template. */
struct PACKED swim_dissemination_header_bin {
	/** mp_encode_map(1) */
	uint8_t m_header;

	/** mp_encode_uint(SWIM_DISSEMINATION) */
	uint8_t k_dissemination;
	/** mp_encode_array() */
	uint8_t m_dissemination;
	uint32_t v_dissemination;
};

/** SWIM member MsgPack template. */
struct PACKED swim_member_bin {
	/** mp_encode_map(1) */
	uint8_t m_header;

	/** mp_encode_uint(SWIM_MEMBER_STATUS) */
	uint8_t k_status;
	/** mp_encode_uint(enum member_status) */
	uint8_t v_status;

	/** mp_encode_uint(SWIM_MEMBER_ADDR_HASH) */
	uint8_t k_addr;
	/** mp_encode_uint((ip << 16) | port) */
	uint8_t m_addr;
	uint64_t v_addr;
};

enum {
	/** How often to send membership messages and pings. */
	HEARTBEAT_RATE_DEFAULT = 1,
	UDP_PACKET_SIZE = 1472,
	DISSEMINATION_BATCH_SIZE =
		(UDP_PACKET_SIZE -
		 sizeof(struct swim_dissemination_header_bin)) /
		sizeof(struct swim_member_bin),
};

/**
 * Members to which a messae should be send next during this
 * round.
 */
static struct rlist queue_next;
/** Generator of broadcast events. */
static struct ev_periodic broadcast_tick;

/** Event dispatcher of incomming messages. */
static struct ev_io input;
/** Event dispatcher of outcomming messages. */
static struct ev_io output;

/**
 * An array of members shuffled on each round and used to rebuild
 * the batch when a member is changed.
 */
static struct swim_member **shuffled_members = NULL;
static int shuffled_members_size = 0;
static struct swim_member *self = NULL;

/**
 * Single broadcast event. It is impossible to have multiple
 * broadcast events at the same time, so it is static and global.
 * Other events are mainly pings and acks, and they can be
 * multiple even for a single member. Therefore they are allocated
 * dynamically.
 */
static struct swim_io_event broadcast_event;

/** Queue of io events ready to push now. */
static struct rlist queue_output;

static inline void
swim_push_broadcast_event()
{
	broadcast_event.type = SWIM_IO_BROADCAST_MEMBERS;
	rlist_add_tail_entry(&queue_output, &broadcast_event, in_queue_output);
	ev_io_start(loop(), &output);
}

/**
 * Register a new member with a specified status. Here it is
 * added to the hash, to the 'next' queue.
 */
static struct swim_member *
swim_member_new(struct sockaddr_in *addr, enum swim_member_status status)
{
	struct swim_member *member =
		(struct swim_member *) malloc(sizeof(*member));
	if (member == NULL) {
		diag_set(OutOfMemory, sizeof(*member), "malloc", "member");
		return NULL;
	}
	member->status = status;
	member->addr = *addr;
	struct mh_i64ptr_node_t node;
	node.key = sockaddr_in_hash(addr);
	node.val = member;
	mh_int_t rc = mh_i64ptr_put(members, &node, NULL, NULL);
	if (rc == mh_end(members)) {
		free(member);
		diag_set(OutOfMemory, sizeof(mh_int_t), "malloc", "node");
		return NULL;
	}
	rlist_add_entry(&queue_next, member, in_queue_next);
	return member;
}

static inline struct swim_member *
swim_find_member(uint64_t hash)
{
	mh_int_t node = mh_i64ptr_find(members, hash, NULL);
	if (node == mh_end(members))
		return NULL;
	return (struct swim_member *) mh_i64ptr_node(members, node)->val;
}

/**
 * Remove the member from all queues, hashes, destroy it and free
 * the memory.
 */
static inline void
swim_member_delete(struct swim_member *member)
{
	uint64_t key = sockaddr_in_hash(&member->addr);
	mh_int_t rc = mh_i64ptr_find(members, key, NULL);
	assert(rc != mh_end(members));
	mh_i64ptr_del(members, rc, NULL);
	rlist_del_entry(member, in_queue_next);
	free(member);
}

static int
swim_shuffle_members()
{
	int new_size = mh_size(members);
	if (shuffled_members_size != new_size) {
		int size = sizeof(shuffled_members[0]) * new_size;
		struct swim_member **new =
			(struct swim_member **) realloc(shuffled_members, size);
		if (new == NULL) {
			diag_set(OutOfMemory, size, "realloc", "new");
			return -1;
		}
		shuffled_members = new;
		shuffled_members_size = new_size;
	}
	int i = 0;
	for (mh_int_t node = mh_first(members), end = mh_end(members);
	     node != end; node = mh_next(members, node), ++i) {
		shuffled_members[i] = (struct swim_member *)
			mh_i64ptr_node(members, node)->val;
		int j = rand() / (RAND_MAX / (i + 1) + 1);
		SWAP(shuffled_members[i], shuffled_members[j]);
	}
	return 0;
}

static int
swim_new_round()
{
	if (swim_shuffle_members() != 0)
		return -1;
	rlist_create(&queue_next);
	for (int i = 0; i < shuffled_members_size; ++i) {
		if (shuffled_members[i] != self) {
			rlist_add_entry(&queue_next, shuffled_members[i],
					in_queue_next);
		}
	}
	return 0;
}

static int
swim_encode_dissemination_msg(char *buffer)
{
	char *start = buffer;
	if ((shuffled_members == NULL || rlist_empty(&queue_next)) &&
	    swim_new_round() != 0)
		return -1;

	struct swim_dissemination_header_bin header_bin;
	int batch_size = MIN(DISSEMINATION_BATCH_SIZE, shuffled_members_size);
	header_bin.m_header = 0x81;

	header_bin.k_dissemination = SWIM_DISSEMINATION;
	header_bin.m_dissemination = 0xdd;
	header_bin.v_dissemination = mp_bswap_u32(batch_size);
	memcpy(buffer, &header_bin, sizeof(header_bin));
	buffer += sizeof(header_bin);

	struct swim_member_bin member_bin;
	member_bin.m_header = 0x82;
	member_bin.k_status = SWIM_MEMBER_STATUS;
	member_bin.k_addr = SWIM_MEMBER_ADDR_HASH;
	member_bin.m_addr = 0xcf;
	for (int i = 0; i < batch_size; ++i) {
		struct swim_member *member = shuffled_members[i];
		member_bin.v_status = member->status;
		member_bin.v_addr =
			mp_bswap_u64(sockaddr_in_hash(&member->addr));
		memcpy(buffer, &member_bin, sizeof(member_bin));
		buffer += sizeof(member_bin);
	}
	return buffer - start;
}

/**
 * Do one broadcast step. Broadcast is manual - there is no
 * SO_BROADCAST usage. Multicast is not supported as well - just
 * manual iterative sending.
 */
static void
swim_send_dissemination_msg()
{
	char buffer[UDP_PACKET_SIZE];
	int size = swim_encode_dissemination_msg(buffer);
	if (size < 0) {
		diag_log();
		return;
	}
	struct swim_member *m =
		rlist_first_entry(&queue_next, struct swim_member,
				  in_queue_next);
	say_info("send to %s",
		 sio_strfaddr((struct sockaddr *) &m->addr, sizeof(m->addr)));
	if (sio_sendto(output.fd, buffer, size, 0, (struct sockaddr *) &m->addr,
		       sizeof(m->addr)) == -1)
		diag_log();
	rlist_del_entry(m, in_queue_next);
	ev_periodic_start(loop(), &broadcast_tick);
}

static void
swim_on_output(struct ev_loop *loop, struct ev_io *io, int events)
{
	assert((events & EV_WRITE) != 0);
	(void) events;
	if (rlist_empty(&queue_output)) {
		ev_io_stop(loop, io);
		return;
	}
	struct swim_io_event *event =
		rlist_shift_entry(&queue_output, struct swim_io_event,
				  in_queue_output);
	assert(event->type == SWIM_IO_BROADCAST_MEMBERS);
	swim_send_dissemination_msg();
	if (rlist_empty(&queue_output)) {
		ev_io_stop(loop, io);
		return;
	}
}

/** Once per specified timeout trigger a next broadcast step. */
static void
swim_trigger_broadcast(struct ev_loop *loop, struct ev_periodic *p, int events)
{
	assert((events & EV_PERIODIC) != 0);
	(void) events;
	swim_push_broadcast_event();
	ev_periodic_stop(loop, p);
}

static int
swim_process_dissemination(const char **pos)
{
	if (mp_typeof(**pos) != MP_ARRAY) {
		say_error("Invalid SWIM message: dissemination should be an "\
			  "array");
		return -1;
	}
	uint64_t size = mp_decode_array(pos);
	for (uint64_t i = 0; i < size; ++i) {
		if (mp_typeof(**pos) != MP_MAP) {
			say_error("Invalid SWIM message: member should be map");
			return -1;
		}
		uint64_t map_size = mp_decode_map(pos);
		enum swim_member_status status = MEMBER_ALIVE;
		uint64_t addr_hash = UINT64_MAX;
		for (uint64_t j = 0; j < map_size; ++j) {
			if (mp_typeof(**pos) != MP_UINT) {
				say_error("Invalid SWIM message: member key "\
					  "should be uint");
				return -1;
			}
			uint64_t key = mp_decode_uint(pos);
			switch(key) {
			case SWIM_MEMBER_STATUS:
				if (mp_typeof(**pos) != MP_UINT) {
					say_error("Invalid SWIM message: "\
						  "member status should be "\
						  "uint");
					return -1;
				}
				key = mp_decode_uint(pos);
				if (key >= swim_member_status_MAX) {
					say_error("Invalid SWIM message: "\
						  "unknown member status");
					return -1;
				}
				status = key;
				break;
			case SWIM_MEMBER_ADDR_HASH:
				if (mp_typeof(**pos) != MP_UINT) {
					say_error("Invalid SWIM message: "\
						  "member address should be "\
						  "uint");
					return -1;
				}
				addr_hash = mp_decode_uint(pos);
				if ((addr_hash >> 48) != 0) {
					say_error("Invalid SWIM message: "\
						  "invalid address");
					return -1;
				}
				break;
			default:
				say_error("Invalid SWIM message: unknown "\
					  "member key");
				return -1;
			}
		}
		struct swim_member *member = swim_find_member(addr_hash);
		if (member != NULL) {
			member->status = status;
		} else {
			struct sockaddr_in addr;
			sockaddr_in_unhash(&addr, addr_hash);
			member = swim_member_new(&addr, status);
			if (member == NULL)
				diag_log();
		}
	}
	return 0;
}

/** Receive and process a new message. */
static void
swim_on_input(struct ev_loop *loop, struct ev_io *io, int events)
{
	assert((events & EV_READ) != 0);
	(void) events;
	(void) loop;
	struct sockaddr_in addr;
	socklen_t len = sizeof(addr);
	char buffer[UDP_PACKET_SIZE];
	if (sio_recvfrom(io->fd, buffer, sizeof(buffer), 0,
			 (struct sockaddr *) &addr, &len) == -1) {
		diag_log();
		return;
	}
	say_info("received from %s",
		 sio_strfaddr((struct sockaddr *) &addr, len));
	const char *pos = buffer;
	if (mp_typeof(*pos) != MP_MAP) {
		say_error("Invalid SWIM message: expected map header");
		return;
	}
	uint64_t map_size = mp_decode_map(&pos);
	for (uint64_t i = 0; i < map_size; ++i) {
		if (mp_typeof(*pos) != MP_UINT) {
			say_error("Invalid SWIM message: header should "\
				  "contain uint keys");
			return;
		}
		if (mp_decode_uint(&pos) != SWIM_DISSEMINATION) {
			say_error("Invalid SWIM message: only dissemination "\
				  "component is supported");
			return;
		}
		if (swim_process_dissemination(&pos) != 0)
			return;
	}
}

/**
 * Convert a string URI like "ip:port" to sockaddr_in structure.
 */
static int
uri_to_addr(const char *str, struct sockaddr_in *addr)
{
	struct uri uri;
	if (uri_parse(&uri, str) != 0 || uri.service == NULL)
		goto invalid_uri;
	in_addr_t iaddr;
	if (uri.host_len == 0 || (uri.host_len == 9 &&
				  memcmp("localhost", uri.host, 9) == 0)) {
		iaddr = htonl(INADDR_ANY);
	} else {
		iaddr = inet_addr(tt_cstr(uri.host, uri.host_len));
		if (iaddr == (in_addr_t) -1)
			goto invalid_uri;
	}
	int port = htons(atoi(uri.service));
	memset(addr, 0, sizeof(*addr));
	addr->sin_family = AF_INET;
	addr->sin_addr.s_addr = iaddr;
	addr->sin_port = port;
	return 0;

invalid_uri:
	diag_set(SocketError, sio_socketname(-1), "invalid uri \"%s\"", str);
	return -1;
}

/**
 * Initialize the module. By default, the module is turned off and
 * does nothing. To start SWIM swim_cfg is used.
 */
static int
swim_init()
{
	members = mh_i64ptr_new();
	if (members == NULL) {
		diag_set(OutOfMemory, sizeof(*members), "malloc",
			 "members");
		return -1;
	}
	ev_init(&input, swim_on_input);
	ev_init(&output, swim_on_output);
	ev_init(&broadcast_tick, swim_trigger_broadcast);
	ev_periodic_set(&broadcast_tick, 0, HEARTBEAT_RATE_DEFAULT, NULL);
	rlist_create(&queue_next);
	rlist_create(&queue_output);
	return 0;
}

int
swim_cfg(const char **member_uris, int member_uri_count, const char *server_uri,
	 double heartbeat_rate)
{
	if (members == NULL && swim_init() != 0)
		return -1;
	struct sockaddr_in addr;
	struct swim_member **new_cfg;
	struct swim_member *new_self = self;
	if (member_uri_count > 0) {
		int size = sizeof(new_cfg[0]) * member_uri_count;
		new_cfg =  (struct swim_member **) malloc(size);
		if (new_cfg == NULL) {
			diag_set(OutOfMemory, size, "malloc", "new_cfg");
			return -1;
		}
	}
	int new_cfg_size = 0;
	for (; new_cfg_size < member_uri_count; ++new_cfg_size) {
		if (uri_to_addr(member_uris[new_cfg_size], &addr) != 0)
			goto error;
		uint64_t hash = sockaddr_in_hash(&addr);
		struct swim_member *member = swim_find_member(hash);
		if (member == NULL) {
			member = swim_member_new(&addr, MEMBER_NEW);
			if (member == NULL)
				goto error;
		}
		new_cfg[new_cfg_size] = member;
	}

	if (server_uri != NULL) {
		if (uri_to_addr(server_uri, &addr) != 0)
			goto error;
		socklen_t addrlen;
		struct sockaddr_in cur_addr;

		if (!ev_is_active(&input) ||
		    getsockname(input.fd, (struct sockaddr *) &cur_addr,
				&addrlen) != 0 ||
		    addr.sin_addr.s_addr != cur_addr.sin_addr.s_addr ||
		    addr.sin_port != cur_addr.sin_port) {
			int fd = sio_socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP);
			if (fd == -1)
				goto error;
			if (sio_bind(fd, (struct sockaddr *) &addr,
				     sizeof(addr)) != 0) {
				close(fd);
				goto error;
			}
			ev_io_set(&input, fd, EV_READ);
			ev_io_set(&output, fd, EV_WRITE);
			ev_io_start(loop(), &input);
			ev_periodic_start(loop(), &broadcast_tick);

			uint64_t self_hash = sockaddr_in_hash(&addr);
			new_self = swim_find_member(self_hash);
			if (new_self == NULL) {
				new_self = swim_member_new(&addr, MEMBER_NEW);
				if (new_self == NULL)
					goto error;
			}
		}
	}

	if (broadcast_tick.interval != heartbeat_rate && heartbeat_rate > 0)
		ev_periodic_set(&broadcast_tick, 0, heartbeat_rate, NULL);

	if (member_uri_count > 0) {
		for (int i = 0; i < new_cfg_size; ++i)
			new_cfg[i]->status = MEMBER_ALIVE;
		free(new_cfg);
	}
	if (new_self->status == MEMBER_NEW)
		new_self->status = MEMBER_ALIVE;
	self = new_self;
	return 0;

error:
	for (int i = 0; i < new_cfg_size; ++i) {
		if (new_cfg[i]->status == MEMBER_NEW) {
			swim_member_delete(new_cfg[i]);
			if (new_self == new_cfg[i])
				new_self = NULL;
		}
	}
	if (member_uri_count > 0)
		free(new_cfg);
	if (new_self != NULL && new_self->status == MEMBER_NEW)
		swim_member_delete(new_self);
	return -1;
}

void
swim_info(struct info_handler *info)
{
	info_begin(info);
	if (members == NULL)
		return;
	for (mh_int_t node = mh_first(members), end = mh_end(members);
	     node != end; node = mh_next(members, node)) {
		struct swim_member *member = (struct swim_member *)
			mh_i64ptr_node(members, node)->val;
		info_table_begin(info,
				 sio_strfaddr((struct sockaddr *) &member->addr,
					      sizeof(member->addr)));
		info_append_str(info, "status",
				swim_member_status_strs[member->status]);
		info_table_end(info);
	}
	info_end(info);
}

void
swim_stop()
{
	if (members == NULL)
		return;
	ev_io_stop(loop(), &output);
	ev_io_stop(loop(), &input);
	close(input.fd);
	ev_periodic_stop(loop(), &broadcast_tick);
	mh_int_t node = mh_first(members);
	while (node != mh_end(members)) {
		struct swim_member *m = (struct swim_member *)
			mh_i64ptr_node(members, node)->val;
		mh_i64ptr_del(members, node, NULL);
		free(m);
		node = mh_first(members);
	}
	mh_i64ptr_delete(members);
	members = NULL;
	free(shuffled_members);
	shuffled_members = NULL;
}
