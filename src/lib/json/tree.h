#ifndef TARANTOOL_JSON_TREE_H_INCLUDED
#define TARANTOOL_JSON_TREE_H_INCLUDED
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
#include <stdbool.h>
#include <stdint.h>
#include "small/rlist.h"
#include "path.h"

#ifdef __cplusplus
extern "C"
{
#endif

struct mh_json_tree_node_t;

/**
 * JSON tree is a hierarchical data structure that organize JSON
 * nodes produced by parser.
 * 1. Numeric records are sorted in ascending order in sibling rlist.
 * 2. Structure key records point to source strings memory.
 * 3. Lookup by path complexity is O(path_len):
 * 	path = path_token1 + .. + path_tokenN
 * 	- Complexity of hash(path_tokenI) - O(strlen(path_tokenN))
 * 	- Complexity of hash lookup - O(1) + strcmp on collision
 */
struct json_tree_node {
	/** Path component represented by this node. */
	struct json_path_node key;
	/** Hash calculated for key field. */
	uint32_t key_hash;
	/**
	 * Children hashtable:
	 * json_path_node -> json_tree_node.
	 */
	struct mh_json_tree_node_t *child_by_path_node;
	/**
	 * Link in json_tree_node::children of the parent node.
	 */
	struct rlist sibling;
	/**
	 * List of child nodes, linked by
	 * json_tree_node::sibling.
	 */
	struct rlist children;
	/** Pointer to parent json_tree_node record. */
	struct json_tree_node *parent;
};

/**
 * Compute the hash value of a JSON path component.
 * @param key JSON path component to compute the hash for.
 * @retval Hash value.
 */
uint32_t
json_path_node_hash(struct json_path_node *key);

/**
 * Init a JSON tree node.
 * @param node JSON tree node to initialize.
 * @param path_node JSON path component the new node will
 *                  represent. May be NULL, in this case
 *                  @node initialized as root record.
 * @param path_node_hash Hash of @path_node, should be calculated
 *                       with json_path_node_hash.
 */
void
json_tree_node_create(struct json_tree_node *node,
		      struct json_path_node *path_node,
		      uint32_t path_node_hash);

/**
 * Destroy a JSON tree node.
 * @param node JSON tree node to destruct.
 */
void
json_tree_node_destroy(struct json_tree_node *node);

/**
 * Return count of JSON tree node direct descendant.
 * Matches the size of the child_by_path_node hashtable.
 * @param node JSON tree node to analyze.
 * @retval Count of descendant.
 */
uint32_t
json_tree_node_children_count(struct json_tree_node *node);

/**
 * Look up a child of a JSON tree node by a path component.
 * @param parent JSON tree node to start lookup with.
 * @param path_node JSON parser node with data.
 * @param path_node_hash Hash of @path_node.
 * @retval not NULL pointer to JSON tree node if any.
 * @retval NULL on nothing found.
 */
struct json_tree_node *
json_tree_lookup_by_path_node(struct json_tree_node *parent,
			      struct json_path_node *path_node,
			      uint32_t path_node_hash);

/**
 * Add a new JSON tree node at the given position in the tree.
 * The parent node must not have a child representing the same
 * path component.
 * @param parent JSON tree parent node.
 * @param node JSON tree node to append.
 * @retval 0 On success, -1 on memory allocation error.
 */
int
json_tree_add(struct json_tree_node *parent,
	      struct json_tree_node *node);

/**
 * Delete a JSON tree node at the given position in the tree.
 * The parent node must have such child.
 * @param parent JSON tree parent node.
 * @param node JSON tree node to add.
 */
void
json_tree_remove(struct json_tree_node *parent,
		 struct json_tree_node *node);

/**
 * Lookup a field by path in given position in the JSON tree.
 * @param parent JSON tree parent node.
 * @param path JSON path string.
 * @param path_len Length of @path.
 * @retval not NULL pointer to leaf record if any.
 */
struct json_tree_node *
json_tree_lookup_by_path(struct json_tree_node *parent,
			 const char *path, uint32_t path_len);

/**
 * Make pre order traversal in JSON tree.
 * @param parent The JSON path tree to walk parent.
 * @param pos Iterator pointer, NULL for initialization.
 * @retval not NULL pointer to next node. NULL if nothing found.
 */
struct json_tree_node *
json_tree_next_pre(struct json_tree_node *parent,
		   struct json_tree_node *pos);

/**
 * Make post order traversal in JSON tree.
 * @param parent The JSON path tree to walk parent.
 * @param pos Iterator pointer, NULL for initialization.
 * @retval not NULL pointer to next node. NULL if nothing found.
 */
struct json_tree_node *
json_tree_next_post(struct json_tree_node *parent,
		    struct json_tree_node *pos);

/** Return entry by json_tree_node item. */
#define json_tree_entry(item, type, member) ({				     \
	const typeof( ((type *)0)->member ) *__mptr = (item);		     \
	(type *)( (char *)__mptr - ((size_t) &((type *)0)->member) ); })

/** Return entry by json_tree_node item or NULL if item is NULL.*/
#define json_tree_entry_safe(item, type, member) ({			     \
	(item) != NULL ? json_tree_entry((item), type, member) : NULL; })

/** Make lookup in tree by path and return entry. */
#define json_tree_lookup_entry_by_path(root, path, path_len, type, member)   \
({struct json_tree_node *__tree_node =					     \
	json_tree_lookup_by_path(&(root)->member, path, path_len);	     \
 __tree_node != NULL ? json_tree_entry(__tree_node, type, member) :	     \
		       NULL; })

/** Make lookup in tree by path_node and return entry. */
#define json_tree_lookup_entry_by_path_node(root, path_node, path_node_hash, \
					    type, member)		     \
({struct json_tree_node *__tree_node =					     \
	json_tree_lookup_by_path_node(&(root)->member, path_node,	     \
				      path_node_hash);			     \
 __tree_node != NULL ? json_tree_entry(__tree_node, type, member) :	     \
		       NULL; })

/** Make pre-order traversal in JSON tree. */
#define json_tree_foreach_pre(item, root)				     \
for ((item) = json_tree_next_pre((root), NULL); (item) != NULL;		     \
     (item) = json_tree_next_pre((root), (item)))

/** Make post-order traversal in JSON tree. */
#define json_tree_foreach_post(item, root)				     \
for ((item) = json_tree_next_post((root), NULL); (item) != NULL;	     \
     (item) = json_tree_next_post((root), (item)))

/**
 * Make safe post-order traversal in JSON tree.
 * Safe for building destructors.
 */
#define json_tree_foreach_safe(item, root)				     \
for (struct json_tree_node *__iter = json_tree_next_post((root), NULL);      \
     (((item) = __iter) && (__iter = json_tree_next_post((root), (item))),   \
     (item) != NULL);)

/** Make post-order traversal in JSON tree and return entry. */
#define json_tree_foreach_entry_pre(item, root, member)			     \
for (struct json_tree_node *__iter =					     \
     json_tree_next_pre(&(root)->member, NULL);				     \
     __iter != NULL && ((item) = json_tree_entry(__iter, typeof(*(root)),    \
					       member));		     \
     __iter = json_tree_next_pre(&(root)->member, __iter))

/** Make pre-order traversal in JSON tree and return entry. */
#define json_tree_foreach_entry_post(item, root, member)		     \
for (struct json_tree_node *__iter =					     \
     json_tree_next_post(&(root)->member, NULL);			     \
     __iter != NULL && ((item) = json_tree_entry(__iter, typeof(*(root)),    \
					       member));		     \
     __iter = json_tree_next_post(&(root)->member, __iter))

/**
 * Make secure post-order traversal in JSON tree and return entry.
 */
#define json_tree_foreach_entry_safe(item, root, member)		     \
for (struct json_tree_node *__tmp_iter, *__iter =			     \
     json_tree_next_post(NULL, &(root)->member);			     \
     __iter != NULL && ((item) = json_tree_entry(__iter, typeof(*(root)),    \
						      member)) &&	     \
     (__iter != NULL && (__tmp_iter =					     \
			 json_tree_next_post(&(root)->member, __iter))),     \
     (__iter != NULL && ((item) = json_tree_entry(__iter, typeof(*(root)),   \
						  member)));		     \
     __iter = __tmp_iter)

#ifdef __cplusplus
}
#endif

#endif /* TARANTOOL_JSON_TREE_H_INCLUDED */
