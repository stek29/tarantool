#!/usr/bin/env tarantool

local tap = require('tap')
local buffer = require('buffer')
local ffi = require('ffi')
local msgpackffi = require('msgpackffi')
local yaml = require('yaml')
local digest = require('digest')
local merger = require('merger')

local function get_merger_inst()
    local field_types = {
        any       = 0,
        unsigned  = 1,
        string    = 2,
        array     = 3,
        number    = 4,
        integer   = 5,
        scalar    = 6,
    }

    -- imitate parts of an index
    local parts = {{
        fieldno = 2,
        type = 'unsigned',
        is_nullable = false,
    }}

    local prepared_parts = {}
    for _, part in ipairs(parts) do
        table.insert(prepared_parts, {
            fieldno = part.fieldno - 1,
            type = field_types[part.type],
        })
    end
    return merger.new(prepared_parts)
end

local function check_merger_inst(merger_inst, test, sources_count)
    local IPROTO_DATA = 48
    local TUPLES_CNT = 100

    local tuples = {}
    local sorted_tuples = {}

    -- prepare N tables with tuples as input for merger and sorted tuples as
    -- expected output of merger
    for i = 1, TUPLES_CNT do
        local id = 'id_' .. tostring(i)
        local num = i
        -- [1, sources_count]
        local guava = digest.guava(i, sources_count) + 1
        local tuple = {id, num, guava}
        if tuples[guava] == nil then
            tuples[guava] = {}
        end
        table.insert(tuples[guava], tuple)
        table.insert(sorted_tuples, tuple)
    end

    -- initialize N buffers; write corresponding tuples to that buffers;
    -- that imitates netbox's select with {buffer = ...}
    local buffers = {}
    for i = 1, sources_count do
        buffers[i] = buffer.ibuf()
        msgpackffi.internal.encode_r(buffers[i], {[IPROTO_DATA] = tuples[i] or {}}, 0)
    end

    -- merge N buffers into res
    local res = {}
    merger_inst:start(buffers, 1)
    while true do
        local tuple = merger_inst:next()
        if tuple == nil then break end
        table.insert(res, tuple:totable())
    end

    test:is_deeply(res, sorted_tuples, ('check order on %d sources'):format(
        sources_count))
end

local test = tap.test('merger')
test:plan(6)
local merger_inst = get_merger_inst()
check_merger_inst(merger_inst, test, 1)
check_merger_inst(merger_inst, test, 2)
check_merger_inst(merger_inst, test, 3)
check_merger_inst(merger_inst, test, 4)
check_merger_inst(merger_inst, test, 5)

-- check more buffers then tuples count
check_merger_inst(merger_inst, test, 1000)

-- XXX: test merger_inst:cmp()

os.exit(test:check() and 0 or 1)
