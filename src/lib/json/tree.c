
/*
 * Copyright 2010-2018 Tarantool AUTHORS: please see AUTHORS file.
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

#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "small/rlist.h"
#include "trivia/util.h"
#include "tree.h"
#include "path.h"
#include "third_party/PMurHash.h"


/**
 * Hash table: json_path_node => json_tree_node.
 */
struct mh_json_tree_node {
	struct json_path_node key;
	uint32_t key_hash;
	struct json_tree_node *node;
};

/**
 * Compare hash records of two json tree nodes. Return 0 if equal.
 */
static inline int
mh_json_tree_node_cmp(const struct mh_json_tree_node *a,
		      const struct mh_json_tree_node *b)
{
	if (a->key.type != b->key.type)
		return a->key.type - b->key.type;
	if (a->key.type == JSON_PATH_STR) {
		if (a->key.len != b->key.len)
			return a->key.len - b->key.len;
		return memcmp(a->key.str, b->key.str, a->key.len);
	} else if (a->key.type == JSON_PATH_NUM) {
		return a->key_hash - b->key_hash;
	}
	unreachable();
}

#define MH_SOURCE 1
#define mh_name _json_tree_node
#define mh_key_t struct mh_json_tree_node *
#define mh_node_t struct mh_json_tree_node
#define mh_arg_t void *
#define mh_hash(a, arg) ((a)->key_hash)
#define mh_hash_key(a, arg) ((a)->key_hash)
#define mh_cmp(a, b, arg) (mh_json_tree_node_cmp((a), (b)))
#define mh_cmp_key(a, b, arg) mh_cmp(a, b, arg)
#include "salad/mhash.h"

static const uint32_t json_path_node_hash_seed = 13U;

uint32_t
json_path_node_hash(struct json_path_node *key)
{
	uint32_t h = json_path_node_hash_seed;
	uint32_t carry = 0;
	const void *data;
	uint32_t data_size;
	if (key->type == JSON_PATH_STR) {
		data = key->str;
		data_size = key->len;
	} else if (key->type == JSON_PATH_NUM) {
		data = &key->num;
		data_size = sizeof(key->num);
	} else {
		unreachable();
	}
	PMurHash32_Process(&h, &carry, data, data_size);
	return PMurHash32_Result(h, carry, data_size);
}

void
json_tree_node_create(struct json_tree_node *node,
		      struct json_path_node *path_node, uint32_t path_node_hash)
{
	assert(path_node == NULL ||
	       path_node_hash == json_path_node_hash(path_node));
	memset(node, 0, sizeof(struct json_tree_node));
	if (path_node != NULL) {
		node->key = *path_node;
		node->key_hash = path_node_hash;
	} else {
		node->key.type = JSON_PATH_END;
	}
	rlist_create(&node->sibling);
	rlist_create(&node->children);
}

uint32_t
json_tree_node_children_count(struct json_tree_node *node)
{
	return node->child_by_path_node != NULL ?
	       mh_size(node->child_by_path_node) : 0;
}

void
json_tree_node_destroy(struct json_tree_node *node)
{
	if (node->child_by_path_node != NULL)
		mh_json_tree_node_delete(node->child_by_path_node);
}

struct json_tree_node *
json_tree_lookup_by_path_node(struct json_tree_node *parent,
			      struct json_path_node *path_node,
			      uint32_t path_node_hash)
{
	if (unlikely(parent->child_by_path_node == NULL))
		return NULL;
	struct mh_json_tree_node info;
	info.key = *path_node;
	info.key_hash = path_node_hash;
	mh_int_t id =
		mh_json_tree_node_find(parent->child_by_path_node, &info, NULL);
	if (id == mh_end(parent->child_by_path_node))
		return NULL;
	struct mh_json_tree_node *ht_node =
		mh_json_tree_node_node(parent->child_by_path_node, id);
	assert(ht_node == NULL || ht_node->node != NULL);
	struct json_tree_node *ret = ht_node != NULL ? ht_node->node : NULL;
	assert(ret == NULL || ret->parent == parent);
	return ret;
}

int
json_tree_add(struct json_tree_node *parent, struct json_tree_node *node)
{
	assert(node->parent == NULL);
	if (unlikely(parent->child_by_path_node == NULL)) {
		parent->child_by_path_node = mh_json_tree_node_new();
		if (parent->child_by_path_node == NULL)
			return -1;
	}
	assert(json_tree_lookup_by_path_node(parent, &node->key,
					     node->key_hash) == NULL);
	struct mh_json_tree_node ht_node;
	ht_node.key = node->key;
	ht_node.key_hash = node->key_hash;
	ht_node.node = node;
	mh_int_t rc = mh_json_tree_node_put(parent->child_by_path_node,
					    &ht_node, NULL, NULL);
	if (rc == mh_end(parent->child_by_path_node))
		return -1;
	node->parent = parent;
	if (node->key.type == JSON_PATH_NUM) {
		/*
		 * Insert an entry into the list, keeping the
		 * numerical values in ascending order.
		 */
		struct json_tree_node *curr_entry = NULL;
		struct rlist *prev_rlist_node = &parent->children;
		rlist_foreach_entry(curr_entry, &parent->children, sibling) {
			assert(curr_entry->key.type == JSON_PATH_NUM);
			if (curr_entry->key.num >= node->key.num)
				break;
			prev_rlist_node = &curr_entry->sibling;
		}
		rlist_add(prev_rlist_node, &node->sibling);
	} else {
		rlist_add(&parent->children, &node->sibling);
	}
	return 0;
}

void
json_tree_remove(struct json_tree_node *parent, struct json_tree_node *node)
{
	assert(node->parent == parent);
	assert(parent->child_by_path_node != NULL);
	assert(json_tree_lookup_by_path_node(parent, &node->key,
					     node->key_hash) == node);
	rlist_del(&node->sibling);
	struct mh_json_tree_node info;
	info.key = node->key;
	info.key_hash = node->key_hash;
	mh_int_t id =
		mh_json_tree_node_find(parent->child_by_path_node, &info, NULL);
	assert(id != mh_end(parent->child_by_path_node));
	mh_json_tree_node_del(parent->child_by_path_node, id, NULL);
	assert(json_tree_lookup_by_path_node(parent, &node->key,
					     node->key_hash) == NULL);
}

struct json_tree_node *
json_tree_lookup_by_path(struct json_tree_node *parent, const char *path,
			 uint32_t path_len)
{
	if (unlikely(parent->child_by_path_node == NULL))
		return NULL;
	int rc;
	struct json_path_parser parser;
	struct json_path_node path_node;
	struct json_tree_node *ret = parent;
	json_path_parser_create(&parser, path, path_len);
	while ((rc = json_path_next(&parser, &path_node)) == 0 &&
	       path_node.type != JSON_PATH_END && ret != NULL) {
		uint32_t path_node_hash = json_path_node_hash(&path_node);
		struct json_tree_node *node =
			json_tree_lookup_by_path_node(ret, &path_node,
						      path_node_hash);
		assert(node == NULL || node->parent == ret);
		ret = node;
	}
	if (rc != 0 || path_node.type != JSON_PATH_END)
		return NULL;
	return ret;
}

static struct json_tree_node *
json_tree_next_child(struct json_tree_node *parent, struct json_tree_node *pos)
{
	struct json_tree_node *next;
	if (pos == NULL) {
		next = rlist_first_entry(&parent->children,
					 struct json_tree_node, sibling);
	} else {
		next = rlist_next_entry(pos, sibling);
	}
	if (&next->sibling != &parent->children)
		return next;
	return NULL;
}

static struct json_tree_node *
json_tree_leftmost(struct json_tree_node *pos)
{
	struct json_tree_node *last;
	do {
		last = pos;
		pos = json_tree_next_child(pos, NULL);
	} while (pos != NULL);
	return last;
}

struct json_tree_node *
json_tree_next_pre(struct json_tree_node *parent, struct json_tree_node *pos)
{
	if (pos == NULL)
		return parent;
	struct json_tree_node *next = json_tree_next_child(pos, NULL);
	if (next != NULL)
		return next;
	while (pos != parent) {
		next = json_tree_next_child(pos->parent, pos);
		if (next != NULL)
			return next;
		pos = pos->parent;
	}
	return NULL;
}

struct json_tree_node *
json_tree_next_post(struct json_tree_node *parent, struct json_tree_node *pos)
{
	struct json_tree_node *next;
	if (pos == NULL)
		return json_tree_leftmost(parent);
	if (pos == parent)
		return NULL;
	next = json_tree_next_child(pos->parent, pos);
	if (next != NULL)
		return json_tree_leftmost(next);
	return pos->parent;
}
