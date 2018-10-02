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
#include "say.h"
#include <stdio.h>
#include <stdlib.h>

#include <lua.h>
#include <lauxlib.h>

#include "lua/utils.h"
#include "small/ibuf.h"
#include "msgpuck.h"

#define HEAP_FORWARD_DECLARATION
#include "salad/heap.h"

#include "box/iproto_constants.h" /* IPROTO_DATA */
#include "box/field_def.h"
#include "box/key_def.h"
#include "box/schema_def.h"
#include "box/tuple.h"
#include "box/lua/tuple.h"
#include "box/box.h"
#include "box/index.h"
#include "src/box/coll_id_cache.h"

#ifndef NDEBUG
#include "say.h"
#endif /* !defined(NDEBUG) */

#include "diag.h"

#define BOX_COLLATION_NAME_INDEX 1

/**
 * Helper macro to throw the out of memory error to Lua.
 */
#define throw_out_of_memory_error(L, size, what_name) do {	\
	diag_set(OutOfMemory, (size), "malloc", (what_name));	\
	luaT_error(L);						\
	unreachable();						\
	return -1;						\
} while(0)

enum source_type_t {
	SOURCE_TYPE_BUFFER,
	SOURCE_TYPE_FUNCTION,
};

struct source {
	struct heap_node hnode;
	enum source_type_t source_type;
	union {
		struct ibuf *buf;
		int next_ref;
	} input;
	size_t remain_len;
	struct tuple *tuple;
};

static uint32_t merger_type_id = 0;

struct merger {
	heap_t heap;
	uint32_t count;
	uint32_t capacity;
	struct source **sources;
	struct key_def *key_def;
	box_tuple_format_t *format;
	int order;
};

static int
lbox_merger_gc(struct lua_State *L);

static bool
source_less(const heap_t *heap, const struct heap_node *a,
	    const struct heap_node *b)
{
	struct source *left = container_of(a, struct source, hnode);
	struct source *right = container_of(b, struct source, hnode);
	if (left->tuple == NULL && right->tuple == NULL)
		return false;
	if (left->tuple == NULL)
		return false;
	if (right->tuple == NULL)
		return true;
	struct merger *merger = container_of(heap, struct merger, heap);
	return merger->order *
	       box_tuple_compare(left->tuple, right->tuple,
				 merger->key_def) < 0;
}

#define HEAP_NAME merger_heap
#define HEAP_LESS source_less
#include "salad/heap.h"

static inline void
source_fetch(struct lua_State *L, struct source *source,
	     box_tuple_format_t *format)
{
	source->tuple = NULL;
	if (source->source_type == SOURCE_TYPE_FUNCTION) {
		lua_rawgeti(L, LUA_REGISTRYINDEX, source->input.next_ref);
		lua_call(L, 0, 1);
		if (lua_isnil(L, -1)) {
			lua_pop(L, 1);
			return;
		}
		source->tuple = luaT_istuple(L, -1);
		if (source->tuple == NULL)
			luaL_error(L, "source_fetch: tuple expected, got %s",
				   lua_typename(L, lua_type(L, -1)));
		lua_pop(L, 1);
	} else {
		if (source->remain_len == 0)
			return;
		--source->remain_len;
		if (ibuf_used(source->input.buf) == 0) {
			luaL_error(L, "Unexpected msgpack buffer end");
		}
		const char *tuple_beg = source->input.buf->rpos;
		const char *tuple_end = tuple_beg;
		mp_next(&tuple_end);
		assert(tuple_end <= source->input.buf->wpos);
		source->input.buf->rpos = (char *) tuple_end;
		source->tuple = box_tuple_new(format, tuple_beg, tuple_end);
	}
	box_tuple_ref(source->tuple);
}

static void
free_sources(struct lua_State *L, struct merger *merger)
{
	for (uint32_t i = 0; i < merger->count; ++i) {
		if (merger->sources[i]->source_type == SOURCE_TYPE_FUNCTION)
			luaL_unref(L, LUA_REGISTRYINDEX,
				   merger->sources[i]->input.next_ref);
		if (merger->sources[i]->tuple != NULL)
			box_tuple_unref(merger->sources[i]->tuple);
		free(merger->sources[i]);
	}
	merger->count = 0;
	free(merger->sources);
	merger->capacity = 0;
	merger_heap_destroy(&merger->heap);
	merger_heap_create(&merger->heap);
}

/**
 * Extract a merger object from a Lua stack.
 */
static struct merger *
check_merger(struct lua_State *L, int idx)
{
	uint32_t cdata_type;
	struct merger **merger_ptr = luaL_checkcdata(L, idx, &cdata_type);
	if (merger_ptr == NULL || cdata_type != merger_type_id)
		return NULL;
	return *merger_ptr;
}

#define RPOS_P(buf) ((const char **) &(buf)->rpos)

/*
 * Skip (and check) the wrapper around tuples array (and the array
 * itself).
 *
 * Expected different kind of wrapping depending of chain_input
 * and chain_first parameters.
 */
static int
skip_input_wrapper(struct ibuf *buf, bool chain_input, bool chain_first,
		   size_t *len_p)
{
	int ok = 1;
	/* Decode {[IPROTO_DATA] = {...}} wrapper. */
	if (!chain_input || chain_first)
		ok = mp_typeof(*buf->rpos) == MP_MAP &&
			mp_decode_map(RPOS_P(buf)) == 1 &&
			mp_typeof(*buf->rpos) == MP_UINT &&
			mp_decode_uint(RPOS_P(buf)) == IPROTO_DATA &&
			mp_typeof(*buf->rpos) == MP_ARRAY;
	/* Decode the array around chained input. */
	if (ok && chain_first)
		ok = mp_decode_array(RPOS_P(buf)) > 0 &&
			mp_typeof(*buf->rpos) == MP_ARRAY;
	/* Decode the array around tuples to merge. */
	if (ok)
		*len_p = mp_decode_array(RPOS_P(buf));
	return ok;
}

#undef RPOS_P

/* Chained mergers
 * ===============
 *
 * Chained mergers are needed to process a batch select request,
 * when one response (buffer) contains several results (tuple
 * arrays) to merge. Reshaping of such results into separate
 * buffers would lead to extra data copies within Lua memory and
 * extra time consuming msgpack decoding, so the merger supports
 * this case of input data shape natively.
 *
 * When @a chain_first option is not provided or is nil the merger
 * expects a usual net.box's select result in each of input
 * buffers.
 *
 * When @a chain_first is provided the merger expects an array of
 * results instead of just result. Pass `true` for the first
 * `start` call and `false` for the following ones. It is possible
 * (but not mandatory) to use different mergers for each result,
 * just reuse the same buffers for consequent `start` calls.
 */
static int
lbox_merger_start(struct lua_State *L)
{
	struct merger *merger;
	int ok =
		(lua_gettop(L) == 3 || lua_gettop(L) == 4) &&
		(merger = check_merger(L, 1)) != NULL &&
		lua_istable(L, 2) == 1 &&
		lua_isnumber(L, 3) == 1 &&
		(lua_isnoneornil(L, 4) == 1 || lua_isboolean(L, 4));
	if (!ok)
		return luaL_error(L, "Bad params, use: start(merger, {buffers}, "
				  "order[, chain_first])");
	merger->order =	lua_tointeger(L, 3) >= 0 ? 1 : -1;
	free_sources(L, merger);

	bool chain_input = !lua_isnoneornil(L, 4);
	bool chain_first = chain_input && lua_toboolean(L, 4);

	merger->capacity = 8;
	const ssize_t sources_size = merger->capacity * sizeof(struct source *);
	merger->sources = (struct source **) malloc(sources_size);
	if (merger->sources == NULL)
		throw_out_of_memory_error(L, sources_size, "merger->sources");
	/* Fetch all sources. */
	while (true) {
		lua_pushinteger(L, merger->count + 1);
		lua_gettable(L, 2);
		if (lua_isnil(L, -1))
			break;
		enum source_type_t source_type;
		struct ibuf *buf = NULL;
		if (lua_isfunction(L, -1)) {
			/* Function input. */
			source_type = SOURCE_TYPE_FUNCTION;
		} else {
			/* Buffer input. */
			source_type = SOURCE_TYPE_BUFFER;
			buf = (struct ibuf *) lua_topointer(L, -1);
			if (buf == NULL)
				break;
			if (ibuf_used(buf) == 0)
				continue;
		}
		/* Shrink sources array if needed. */
		if (merger->count == merger->capacity) {
			merger->capacity *= 2;
			struct source **new_sources;
			const ssize_t new_sources_size =
				merger->capacity * sizeof(struct source *);
			new_sources = (struct source **) realloc(
				merger->sources, new_sources_size);
			if (new_sources == NULL) {
				free_sources(L, merger);
				throw_out_of_memory_error(L, new_sources_size,
							  "new_sources");
			}
			merger->sources = new_sources;
		}
		/* Allocate the new source. */
		merger->sources[merger->count] =
			(struct source *) malloc(sizeof(struct source));
		if (merger->sources[merger->count] == NULL) {
			free_sources(L, merger);
			throw_out_of_memory_error(L, sizeof(struct source),
						  "source");
		}
		merger->sources[merger->count]->source_type = source_type;

		if (source_type == SOURCE_TYPE_FUNCTION) {
			/* Save a function to get next tuple. */
			lua_pushvalue(L, -1); /* duplicate the function */
			int next = luaL_ref(L, LUA_REGISTRYINDEX);
			merger->sources[merger->count]->input.next_ref = next;
		} else {
			size_t *len_p =
				&merger->sources[merger->count]->remain_len;
			if (!skip_input_wrapper(buf, chain_input, chain_first,
						len_p)) {
				free_sources(L, merger);
				return luaL_error(L, "Invalid merge source");
			}
			merger->sources[merger->count]->input.buf = buf;
		}
		merger->sources[merger->count]->tuple = NULL;
		source_fetch(L, merger->sources[merger->count], merger->format);
		const struct tuple *tuple =
		    merger->sources[merger->count]->tuple;
#ifndef NDEBUG
		if (tuple != NULL) {
		    say_debug("merger: [source %p] initial fetch; tuple: %s",
			      merger->sources[merger->count],
			      tuple_str(tuple));
		}
#endif /* !defined(NDEBUG) */
		if (tuple != NULL)
			merger_heap_insert(
				&merger->heap,
				&merger->sources[merger->count]->hnode);
		++merger->count;
	}
	lua_pushboolean(L, true);
	return 1;
}

static int
lbox_merger_next(struct lua_State *L)
{
	struct merger *merger;
	if (lua_gettop(L) != 1 || (merger = check_merger(L, 1)) == NULL)
		return luaL_error(L, "Bad params, use: next(merger)");
	struct heap_node *hnode = merger_heap_top(&merger->heap);
	if (hnode == NULL) {
		lua_pushnil(L);
		return 1;
	}
	struct source *source = container_of(hnode, struct source, hnode);
	luaT_pushtuple(L, source->tuple);
	box_tuple_unref(source->tuple);
	source_fetch(L, source, merger->format);
#ifndef NDEBUG
	if (source->tuple == NULL)
		say_debug("merger: [source %p] delete", source);
	else
		say_debug("merger: [source %p] update; tuple: %s", source,
			  tuple_str(source->tuple));
#endif /* !defined(NDEBUG) */
	if (source->tuple == NULL)
		merger_heap_delete(&merger->heap, hnode);
	else
		merger_heap_update(&merger->heap, hnode);
	return 1;
}

static uint32_t
coll_id_by_name(const char *name, size_t len)
{
	uint32_t size = mp_sizeof_array(1) + mp_sizeof_str(len);
	char begin[size];
	char *end_p = mp_encode_array(begin, 1);
	end_p = mp_encode_str(end_p, name, len);
	box_tuple_t *tuple;
	if (box_index_get(BOX_COLLATION_ID, BOX_COLLATION_NAME_INDEX,
	    begin, end_p, &tuple) != 0)
		return COLL_NONE;
	if (tuple == NULL)
		return COLL_NONE;
	uint32_t result = COLL_NONE;
	(void) tuple_field_u32(tuple, BOX_COLLATION_FIELD_ID, &result);
	return result;
}

static int
lbox_merger_new(struct lua_State *L)
{
	if (lua_gettop(L) != 1 || lua_istable(L, 1) != 1)
		return luaL_error(L, "Bad params, use: new({"
				  "{fieldno = fieldno, type = type"
				  "[, is_nullable = is_nullable"
				  "[, collation_id = collation_id"
				  "[, collation = collation]]]}, ...}");
	uint16_t count = 0, capacity = 8;

	const ssize_t parts_size = sizeof(struct key_part_def) * capacity;
	struct key_part_def *parts = NULL;
	parts = (struct key_part_def *) malloc(parts_size);
	if (parts == NULL)
		throw_out_of_memory_error(L, parts_size, "parts");

	while (true) {
		lua_pushinteger(L, count + 1);
		lua_gettable(L, 1);
		if (lua_isnil(L, -1))
			break;

		/* Extend parts if necessary. */
		if (count == capacity) {
			capacity *= 2;
			struct key_part_def *old_parts = parts;
			const ssize_t parts_size =
				sizeof(struct key_part_def) * capacity;
			parts = (struct key_part_def *) realloc(parts,
								parts_size);
			if (parts == NULL) {
				free(old_parts);
				throw_out_of_memory_error(L, parts_size,
							  "parts");
			}
		}

		/* Set parts[count].fieldno. */
		lua_pushstring(L, "fieldno");
		lua_gettable(L, -2);
		if (lua_isnil(L, -1)) {
			free(parts);
			return luaL_error(L, "fieldno must not be nil");
		}
		/* Transform one-based Lua fieldno to zero-based
		 * C fieldno. */
		parts[count].fieldno = lua_tointeger(L, -1) - 1;
		lua_pop(L, 1);

		/* Set parts[count].type. */
		lua_pushstring(L, "type");
		lua_gettable(L, -2);
		if (lua_isnil(L, -1)) {
			free(parts);
			return luaL_error(L, "type must not be nil");
		}
		size_t type_len;
		const char *type_name = lua_tolstring(L, -1, &type_len);
		lua_pop(L, 1);
		parts[count].type = field_type_by_name(type_name, type_len);
		if (parts[count].type == field_type_MAX) {
			free(parts);
			return luaL_error(L, "Unknown field type: %s",
					  type_name);
		}

		/* Set parts[count].is_nullable. */
		lua_pushstring(L, "is_nullable");
		lua_gettable(L, -2);
		if (lua_isnil(L, -1))
			parts[count].is_nullable = false;
		else
			parts[count].is_nullable = lua_toboolean(L, -1);
		lua_pop(L, 1);

		/* Set parts[count].coll_id using collation_id. */
		lua_pushstring(L, "collation_id");
		lua_gettable(L, -2);
		if (lua_isnil(L, -1))
			parts[count].coll_id = COLL_NONE;
		else
			parts[count].coll_id = lua_tointeger(L, -1);
		lua_pop(L, 1);

		/* Set parts[count].coll_id using collation. */
		lua_pushstring(L, "collation");
		lua_gettable(L, -2);
		/* Check whether box.cfg{} was called. */
		if ((parts[count].coll_id != COLL_NONE || !lua_isnil(L, -1)) &&
		    !box_is_configured()) {
			free(parts);
			return luaL_error(L, "Cannot use collations: "
					  "please call box.cfg{}");
		}
		if (!lua_isnil(L, -1)) {
			if (parts[count].coll_id != COLL_NONE) {
				free(parts);
				return luaL_error(
					L, "Conflicting options: collation_id "
					"and collation");
			}
			size_t coll_name_len;
			const char *coll_name = lua_tolstring(L, -1,
							      &coll_name_len);
			parts[count].coll_id = coll_id_by_name(coll_name,
							       coll_name_len);
			if (parts[count].coll_id == COLL_NONE) {
				free(parts);
				return luaL_error(
					L, "Unknown collation: \"%s\"",
					coll_name);
			}
		}
		lua_pop(L, 1);

		/* Check coll_id. */
		struct coll_id *coll_id = coll_by_id(parts[count].coll_id);
		if (parts[count].coll_id != COLL_NONE && coll_id == NULL) {
			free(parts);
			return luaL_error(L, "Unknown collation_id: %d",
					  parts[count].coll_id);
		}

		++count;
	}

	struct merger *merger = calloc(1, sizeof(*merger));
	if (merger == NULL) {
		free(parts);
		throw_out_of_memory_error(L, sizeof(*merger), "merger");
	}
	merger->key_def = key_def_new(parts, count);
	if (merger->key_def == NULL) {
		free(parts);
		return luaL_error(L, "Cannot create merger->key_def");
	}
	free(parts);

	merger->format = box_tuple_format_new(&merger->key_def, 1);
	if (merger->format == NULL) {
		box_key_def_delete(merger->key_def);
		free(merger);
		return luaL_error(L, "Cannot create merger->format");
	}

	*(struct merger **) luaL_pushcdata(L, merger_type_id) = merger;

	lua_pushcfunction(L, lbox_merger_gc);
	luaL_setcdatagc(L, -2);

	return 1;
}

static int
lbox_merger_cmp(struct lua_State *L)
{
	struct merger *merger;
	if (lua_gettop(L) != 2 ||
	    (merger = check_merger(L, 1)) == NULL)
		return luaL_error(L, "Bad params, use: cmp(merger, key)");
	const char *key = lua_tostring(L, 2);
	struct heap_node *hnode = merger_heap_top(&merger->heap);
	if (hnode == NULL) {
		lua_pushnil(L);
		return 1;
	}
	struct source *source = container_of(hnode, struct source, hnode);
	lua_pushinteger(L, box_tuple_compare_with_key(source->tuple, key,
						      merger->key_def) *
			   merger->order);
	return 1;
}

static int
lbox_merger_gc(struct lua_State *L)
{
	struct merger *merger;
	if ((merger = check_merger(L, 1)) == NULL)
		return 0;
	free_sources(L, merger);
	box_key_def_delete(merger->key_def);
	box_tuple_format_unref(merger->format);
	free(merger);
	return 0;
}

LUA_API int
luaopen_merger(lua_State *L)
{
	luaL_cdef(L, "struct merger;");
	merger_type_id = luaL_ctypeid(L, "struct merger&");
	lua_newtable(L);
	static const struct luaL_Reg meta[] = {
		{"new", lbox_merger_new},
		{NULL, NULL}
	};
	luaL_register_module(L, "merger", meta);

	/* Export C functions to Lua. */
	lua_newtable(L); /* merger.internal */
	lua_pushcfunction(L, lbox_merger_start);
	lua_setfield(L, -2, "start");
	lua_pushcfunction(L, lbox_merger_cmp);
	lua_setfield(L, -2, "cmp");
	lua_pushcfunction(L, lbox_merger_next);
	lua_setfield(L, -2, "next");
	lua_setfield(L, -2, "internal");

	return 1;
}
