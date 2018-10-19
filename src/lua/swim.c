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

#include "utils.h"
#include "diag.h"
#include "swim/swim.h"
#include "small/ibuf.h"
#include "lua/info.h"
#include <info.h>

static int
lua_swim_cfg(struct lua_State *L)
{
	if (lua_gettop(L) != 1)
		return luaL_error(L, "Usage: swim.cfg({<config>})");
	lua_getfield(L, 1, "members");
	const char **member_uris;
	int member_count;
	if (lua_istable(L, -1)) {
		member_count = lua_objlen(L, -1);
		if (member_count > 0) {
			ibuf_reset(tarantool_lua_ibuf);
			int size = sizeof(member_uris[0]) * member_count;
			member_uris = ibuf_alloc(tarantool_lua_ibuf, size);
			if (member_uris == NULL) {
				diag_set(OutOfMemory, size, "ibuf_alloc",
					 "member_uris");
				return luaT_error(L);
			}
			for (int i = 0; i < member_count; ++i) {
				lua_rawgeti(L, -1, i + 1);
				if (! lua_isstring(L, -1)) {
					return luaL_error(L, "Member should "\
							  "be string URI");
				}
				member_uris[i] = lua_tostring(L, -1);
				lua_pop(L, 1);
			}
		}
	} else if (lua_isnil(L, -1)) {
		member_uris = NULL;
		member_count = 0;
	} else {
		return luaL_error(L, "Members should be array");
	}
	lua_pop(L, 1);

	const char *server_uri;
	lua_getfield(L, 1, "server");
	if (lua_isstring(L, -1))
		server_uri = lua_tostring(L, -1);
	else if (lua_isnil(L, -1))
		server_uri = NULL;
	else
		return luaL_error(L, "Server should be string URI");
	lua_pop(L, 1);

	double heartbeat_rate;
	lua_getfield(L, 1, "heartbeat");
	if (lua_isnumber(L, -1)) {
		heartbeat_rate = lua_tonumber(L, -1);
		if (heartbeat_rate <= 0) {
			return luaL_error(L, "Heartbeat should be positive "\
					  "number");
		}
	} else if (! lua_isnil(L, -1)) {
		return luaL_error(L, "Heartbeat should be positive number");
	} else {
		heartbeat_rate = -1;
	}
	lua_pop(L, 1);

	if (swim_cfg(member_uris, member_count, server_uri, heartbeat_rate) != 0) {
		lua_pushnil(L);
		luaT_pusherror(L, diag_last_error(diag_get()));
		return 2;
	}
	lua_pushboolean(L, true);
	return 1;
}

static int
lua_swim_stop(struct lua_State *L)
{
	(void) L;
	swim_stop();
	return 0;
}

static int
lua_swim_info(struct lua_State *L)
{
	struct info_handler info;
	luaT_info_handler_create(&info, L);
	swim_info(&info);
	return 1;
}

void
tarantool_lua_swim_init(struct lua_State *L)
{
	static const struct luaL_Reg lua_swim_methods [] = {
		{"cfg", lua_swim_cfg},
		{"stop", lua_swim_stop},
		{"info", lua_swim_info},
		{NULL, NULL}
	};
	luaL_register_module(L, "swim", lua_swim_methods);
	lua_pop(L, 1);
};
