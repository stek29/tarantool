#ifndef TARANTOOL_BOX_MEMTX_SPACE_H_INCLUDED
#define TARANTOOL_BOX_MEMTX_SPACE_H_INCLUDED
/*
 * Copyright 2010-2016, Tarantool AUTHORS, please see AUTHORS file.
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
#include "space.h"

#if defined(__cplusplus)
extern "C" {
#endif /* defined(__cplusplus) */

struct memtx_engine;

struct memtx_space {
	struct space base;
	/* Number of bytes used in memory by tuples in the space. */
	size_t bsize;
	/**
	 * A pointer to replace function, set to different values
	 * at different stages of recovery.
	 */
	int (*replace)(struct space *, struct tuple *, struct tuple *,
		       enum dup_replace_mode, struct tuple **);
};

/**
 * Change binary size of a space subtracting old tuple's size and
 * adding new tuple's size. Used also for rollback by swaping old
 * and new tuple.
 *
 * @param space Instance of memtx space.
 * @param old_tuple Old tuple (replaced or deleted).
 * @param new_tuple New tuple (inserted).
 */
void
memtx_space_update_bsize(struct space *space,
			 const struct tuple *old_tuple,
			 const struct tuple *new_tuple);

int
memtx_space_replace_no_keys(struct space *, struct tuple *, struct tuple *,
			    enum dup_replace_mode, struct tuple **);
int
memtx_space_replace_build_next(struct space *, struct tuple *, struct tuple *,
			       enum dup_replace_mode, struct tuple **);
int
memtx_space_replace_primary_key(struct space *, struct tuple *, struct tuple *,
				enum dup_replace_mode, struct tuple **);
int
memtx_space_replace_all_keys(struct space *, struct tuple *, struct tuple *,
			     enum dup_replace_mode, struct tuple **);

struct space *
memtx_space_new(struct memtx_engine *memtx,
		struct space_def *def, struct rlist *key_list, uint64_t epoch);

#if defined(__cplusplus)
} /* extern "C" */
#endif /* defined(__cplusplus) */

#endif /* TARANTOOL_BOX_MEMTX_SPACE_H_INCLUDED */
