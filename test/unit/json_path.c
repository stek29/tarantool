#include "json/path.h"
#include "json/tree.h"
#include "unit.h"
#include "trivia/util.h"
#include <string.h>
#include <stdbool.h>

#define reset_to_new_path(value) \
	path = value; \
	len = strlen(value); \
	json_path_parser_create(&parser, path, len);

#define is_next_index(value_len, value) \
	path = parser.src + parser.offset; \
	is(json_path_next(&parser, &node), 0, "parse <%." #value_len "s>", \
	   path); \
	is(node.type, JSON_PATH_NUM, "<%." #value_len "s> is num", path); \
	is(node.num, value, "<%." #value_len "s> is " #value, path);

#define is_next_key(value) \
	len = strlen(value); \
	is(json_path_next(&parser, &node), 0, "parse <" value ">"); \
	is(node.type, JSON_PATH_STR, "<" value "> is str"); \
	is(node.len, len, "len is %d", len); \
	is(strncmp(node.str, value, len), 0, "str is " value);

void
test_basic()
{
	header();
	plan(71);
	const char *path;
	int len;
	struct json_path_parser parser;
	struct json_path_node node;

	reset_to_new_path("[0].field1.field2['field3'][5]");
	is_next_index(3, 0);
	is_next_key("field1");
	is_next_key("field2");
	is_next_key("field3");
	is_next_index(3, 5);

	reset_to_new_path("[3].field[2].field")
	is_next_index(3, 3);
	is_next_key("field");
	is_next_index(3, 2);
	is_next_key("field");

	reset_to_new_path("[\"f1\"][\"f2'3'\"]");
	is_next_key("f1");
	is_next_key("f2'3'");

	/* Support both '.field1...' and 'field1...'. */
	reset_to_new_path(".field1");
	is_next_key("field1");
	reset_to_new_path("field1");
	is_next_key("field1");

	/* Long number. */
	reset_to_new_path("[1234]");
	is_next_index(6, 1234);

	/* Empty path. */
	reset_to_new_path("");
	is(json_path_next(&parser, &node), 0, "parse empty path");
	is(node.type, JSON_PATH_END, "is str");

	/* Path with no '.' at the beginning. */
	reset_to_new_path("field1.field2");
	is_next_key("field1");

	/* Unicode. */
	reset_to_new_path("[2][6]['привет中国world']['中国a']");
	is_next_index(3, 2);
	is_next_index(3, 6);
	is_next_key("привет中国world");
	is_next_key("中国a");

	check_plan();
	footer();
}

#define check_new_path_on_error(value, errpos) \
	reset_to_new_path(value); \
	struct json_path_node node; \
	is(json_path_next(&parser, &node), errpos, "error on position %d" \
	   " for <%s>", errpos, path);

struct path_and_errpos {
	const char *path;
	int errpos;
};

void
test_errors()
{
	header();
	plan(20);
	const char *path;
	int len;
	struct json_path_parser parser;
	const struct path_and_errpos errors[] = {
		/* Double [[. */
		{"[[", 2},
		/* Not string inside []. */
		{"[field]", 2},
		/* String outside of []. */
		{"'field1'.field2", 1},
		/* Empty brackets. */
		{"[]", 2},
		/* Empty string. */
		{"''", 1},
		/* Spaces between identifiers. */
		{" field1", 1},
		/* Start from digit. */
		{"1field", 1},
		{".1field", 2},
		/* Unfinished identifiers. */
		{"['field", 8},
		{"['field'", 9},
		{"[123", 5},
		{"['']", 3},
		/*
		 * Not trivial error: can not write
		 * '[]' after '.'.
		 */
		{".[123]", 2},
		/* Misc. */
		{"[.]", 2},
		/* Invalid UNICODE */
		{"['aaa\xc2\xc2']", 6},
		{".\xc2\xc2", 2},
	};
	for (size_t i = 0; i < lengthof(errors); ++i) {
		reset_to_new_path(errors[i].path);
		int errpos = errors[i].errpos;
		struct json_path_node node;
		is(json_path_next(&parser, &node), errpos,
		   "error on position %d for <%s>", errpos, path);
	}

	reset_to_new_path("f.[2]")
	struct json_path_node node;
	json_path_next(&parser, &node);
	is(json_path_next(&parser, &node), 3, "can not write <field.[index]>")

	reset_to_new_path("f.")
	json_path_next(&parser, &node);
	is(json_path_next(&parser, &node), 3, "error in leading <.>");

	reset_to_new_path("fiel d1")
	json_path_next(&parser, &node);
	is(json_path_next(&parser, &node), 5, "space inside identifier");

	reset_to_new_path("field\t1")
	json_path_next(&parser, &node);
	is(json_path_next(&parser, &node), 6, "tab inside identifier");

	check_plan();
	footer();
}

struct test_struct {
	int value;
	struct json_tree_node tree_node;
};

struct test_struct *
test_add_path(struct test_struct *root, const char *path, uint32_t path_len,
	      struct test_struct *records_pool, int *pool_idx)
{
	int rc;
	struct json_path_parser parser;
	struct json_path_node path_node;
	struct test_struct *parent = root;
	json_path_parser_create(&parser, path, path_len);
	while ((rc = json_path_next(&parser, &path_node)) == 0 &&
		path_node.type != JSON_PATH_END) {
		uint32_t path_node_hash = json_path_node_hash(&path_node);
		struct test_struct *new_node =
			json_tree_lookup_entry_by_path_node(parent, &path_node,
							    path_node_hash,
							    struct test_struct,
							    tree_node);
		if (new_node == NULL) {
			new_node = &records_pool[*pool_idx];
			*pool_idx = *pool_idx + 1;
			json_tree_node_create(&new_node->tree_node, &path_node,
					      path_node_hash);
			rc = json_tree_add(&parent->tree_node,
					   &new_node->tree_node);
			fail_if(rc != 0);
		}
		parent = new_node;
	}
	fail_if(rc != 0 || path_node.type != JSON_PATH_END);
	return parent;
}

void
test_tree()
{
	header();
	plan(42);

	struct test_struct records[6];
	for (int i = 0; i < 6; i++)
		records[i].value = i;
	json_tree_node_create(&records[0].tree_node, NULL, 0);
	fail_if(&records[0] != json_tree_entry(&records[0].tree_node,
					       struct test_struct, tree_node));

	const char *path1 = "[1][10]";
	const char *path2 = "[1][20].file";
	const char *path3_to_remove = "[2]";
	const char *path_unregistered = "[1][3]";

	int records_idx = 1;
	struct test_struct *node;
	node = test_add_path(&records[0], path1, strlen(path1), records,
			     &records_idx);
	is(node, &records[2], "add path '%s'", path1);

	node = test_add_path(&records[0], path2, strlen(path2), records,
			     &records_idx);
	is(node, &records[4], "add path '%s'", path2);

	node = json_tree_lookup_entry_by_path(&records[0], path1, strlen(path1),
					      struct test_struct, tree_node);
	is(node, &records[2], "lookup path '%s'", path1);

	node = json_tree_lookup_entry_by_path(&records[0], path2, strlen(path2),
					      struct test_struct, tree_node);
	is(node, &records[4], "lookup path '%s'", path2);

	node = json_tree_lookup_entry_by_path(&records[0], path_unregistered,
					      strlen(path_unregistered),
					      struct test_struct, tree_node);
	is(node, NULL, "lookup unregistered path '%s'", path_unregistered);

	node = test_add_path(&records[0], path3_to_remove,
			     strlen(path3_to_remove), records, &records_idx);
	is(node, &records[5], "add path to remove '%s'", path3_to_remove);
	if (node != NULL) {
		json_tree_remove(&records[0].tree_node, &node->tree_node);
		json_tree_node_destroy(&node->tree_node);
	} else {
		isnt(node, NULL, "can't remove empty node!");
	}

	/* Test iterators. */
	struct json_tree_node *tree_record = NULL;
	const struct json_tree_node *tree_nodes_preorder[] =
		{&records[0].tree_node, &records[1].tree_node,
		 &records[2].tree_node, &records[3].tree_node,
		 &records[4].tree_node};
	int cnt = sizeof(tree_nodes_preorder)/sizeof(tree_nodes_preorder[0]);
	int idx = 0;
	json_tree_foreach_pre(tree_record, &records[0].tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t1 =
			json_tree_entry(tree_record, struct test_struct,
					tree_node);
		struct test_struct *t2 =
			json_tree_entry(tree_nodes_preorder[idx],
					struct test_struct, tree_node);
		is(tree_record, tree_nodes_preorder[idx],
		   "test foreach pre order %d: have %d expected %d",
		   idx, t1->value, t2->value);
		++idx;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);


	const struct json_tree_node *tree_nodes_postorder[] =
		{&records[2].tree_node, &records[4].tree_node, &records[3].tree_node,
		 &records[1].tree_node,
		 &records[0].tree_node};
	cnt = sizeof(tree_nodes_postorder)/sizeof(tree_nodes_postorder[0]);
	idx = 0;
	json_tree_foreach_post(tree_record, &records[0].tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t1 =
			json_tree_entry(tree_record, struct test_struct,
					tree_node);
		struct test_struct *t2 =
			json_tree_entry(tree_nodes_postorder[idx],
					struct test_struct, tree_node);
		is(tree_record, tree_nodes_postorder[idx],
		   "test foreach post order %d: have %d expected of %d",
		   idx, t1->value, t2->value);
		++idx;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);

	idx = 0;
	json_tree_foreach_safe(tree_record, &records[0].tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t1 =
			json_tree_entry(tree_record, struct test_struct,
					tree_node);
		struct test_struct *t2 =
			json_tree_entry(tree_nodes_postorder[idx],
					struct test_struct, tree_node);
		is(tree_record, tree_nodes_postorder[idx],
		   "test foreach safe order %d: have %d expected of %d",
		   idx, t1->value, t2->value);
		++idx;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);

	idx = 0;
	json_tree_foreach_entry_pre(node, &records[0], tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t =
			json_tree_entry(tree_nodes_preorder[idx],
					struct test_struct, tree_node);
		is(&node->tree_node, tree_nodes_preorder[idx],
		   "test foreach entry pre order %d: have %d expected of %d",
		   idx, node->value, t->value);
		idx++;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);

	idx = 0;
	json_tree_foreach_entry_post(node, &records[0], tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t =
			json_tree_entry(tree_nodes_postorder[idx],
					struct test_struct, tree_node);
		is(&node->tree_node, tree_nodes_postorder[idx],
		   "test foreach entry post order %d: have %d expected of %d",
		   idx, node->value, t->value);
		idx++;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);

	idx = 0;
	json_tree_foreach_entry_safe(node, &records[0], tree_node) {
		if (idx >= cnt)
			break;
		struct test_struct *t =
			json_tree_entry(tree_nodes_postorder[idx],
					struct test_struct, tree_node);
		is(&node->tree_node, tree_nodes_postorder[idx],
		   "test foreach entry safe order %d: have %d expected of %d",
		   idx, node->value, t->value);
		json_tree_node_destroy(&node->tree_node);
		idx++;
	}
	is(idx, 5, "records iterated count %d of %d", idx, cnt);

	check_plan();
	footer();
}

void
test_normalize_path()
{
	header();
	plan(8);

	const char *path_normalized = "[\"FIO\"][3][\"fname\"]";
	const char *path1 = "FIO[3].fname";
	const char *path2 = "[\"FIO\"][3].fname";
	const char *path3 = "FIO[3][\"fname\"]";
	char buff[strlen(path_normalized) + 1];
	int rc;

	rc = json_path_normalize(path_normalized, strlen(path_normalized),
				 buff);
	is(rc, 0, "normalize '%s' path status", path_normalized);
	is(strcmp(buff, path_normalized), 0, "normalize '%s' path compare",
		  path_normalized);

	rc = json_path_normalize(path1, strlen(path1), buff);
	is(rc, 0, "normalize '%s' path status", path1);
	is(strcmp(buff, path_normalized), 0, "normalize '%s' path compare",
		  path1);

	rc = json_path_normalize(path2, strlen(path2), buff);
	is(rc, 0, "normalize '%s' path status", path2);
	is(strcmp(buff, path_normalized), 0, "normalize '%s' path compare",
		  path2);

	rc = json_path_normalize(path3, strlen(path3), buff);
	is(rc, 0, "normalize '%s' path status", path3);
	is(strcmp(buff, path_normalized), 0, "normalize '%s' path compare",
		  path3);

	check_plan();
	footer();
}

int
main()
{
	header();
	plan(4);

	test_basic();
	test_errors();
	test_tree();
	test_normalize_path();

	int rc = check_plan();
	footer();
	return rc;
}
