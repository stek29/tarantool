/*
 * Copyright 2010-2017, Tarantool AUTHORS, please see AUTHORS file.
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
#include "journal.h"
#include <small/region.h>
#include <fiber.h>
#include <diag.h>

/**
 * Used to load from a memtx snapshot. LSN is not used,
 * but txn_commit() must work.
 */
static int64_t
dummy_journal_write(struct journal *journal, struct journal_entry *entry)
{
	(void) journal;
	(void) entry;
	return 0;
}

static struct journal dummy_journal = {
	dummy_journal_write,
	NULL,
};

struct journal *current_journal = &dummy_journal;

struct journal_entry *
journal_entry_new(size_t n_rows)
{
	struct journal_entry *entry;

	size_t size = (sizeof(struct journal_entry) +
		       sizeof(entry->rows[0]) * n_rows);

	entry = region_aligned_alloc(&fiber()->gc, size,
				     alignof(struct journal_entry));
	if (entry == NULL) {
		diag_set(OutOfMemory, size, "region", "struct journal_entry");
		return NULL;
	}
	entry->len = 0;
	entry->n_rows = n_rows;
	entry->res = -1;
	entry->fiber = fiber();
	return entry;
}

