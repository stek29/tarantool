#!/usr/bin/env tarantool

local tap = require('tap')
local buffer = require('buffer')
local msgpackffi = require('msgpackffi')
local digest = require('digest')
local merger = require('merger')
local crypto = require('crypto')
local fiber = require('fiber')

local IPROTO_DATA = 48

local schemas = {
    {
        name = 'small_unsigned',
        parts = {
            {
                fieldno = 2,
                type = 'unsigned',
            }
        },
        gen_tuple = function(tupleno)
            return {'id_' .. tostring(tupleno), tupleno}
        end,
    },
    {
        name = 'small_string',
        parts = {
            {
                fieldno = 1,
                type = 'string',
            }
        },
        gen_tuple = function(tupleno)
            return {'id_' .. tostring(tupleno)}
        end,
    },
    {
        name = 'huge_string',
        parts = {
            {
                fieldno = 17,
                type = 'string',
            },
            {
                fieldno = 4,
                type = 'string',
            },
            {
                fieldno = 12,
                type = 'string',
            },
        },
        gen_tuple = function(tupleno)
            local res = {}
            for fieldno = 1, 20 do
                res[fieldno] = crypto.digest.sha256(('%d;%d'):format(tupleno,
                                                                     fieldno))
            end
            return res
        end,
    },
    {
        name = 'huge_string_eq_3',
        parts = {
            {
                fieldno = 17,
                type = 'string',
            },
            {
                fieldno = 4,
                type = 'string',
            },
            {
                fieldno = 12,
                type = 'string',
            },
        },
        gen_tuple = function(tupleno)
            local res = {}
            for fieldno = 1, 20 do
                if fieldno == 17 then
                    res[fieldno] = 'field_17'
                elseif fieldno == 4 then
                    res[fieldno] = 'field_4'
                else
                    res[fieldno] = crypto.digest.sha256(('%d;%d'):format(
                        tupleno, fieldno))
                end
            end
            return res
        end,
    },
    -- Merger allocates a memory for 8 parts by default.
    -- Test that reallocation works properly.
    {
        name = 'many_parts',
        parts = (function()
            local parts = {}
            for i = 1, 128 do
                parts[i] = {
                    fieldno = i,
                    type = 'unsigned',
                }
            end
            return parts
        end)(),
        gen_tuple = function(i)
            local tuple = {}
            for i = 1, 128 do
                tuple[i] = i
            end
            return tuple
        end,
    },
    -- Test null value in nullable field of an index.
    {
        name = 'nullable',
        parts = {
            {
                fieldno = 1,
                type = 'unsigned',
            },
            {
                fieldno = 2,
                type = 'string',
                is_nullable = true,
            },
        },
        gen_tuple = function(i)
            if i % 1 == 1 then
                return {i, tostring(i)}
            else
                return {i, box.NULL}
            end
        end,
    },
}

local function get_index_fields_position(parts)
    local res = {}
    for _, part in ipairs(parts) do
        table.insert(res, part.fieldno)
    end
    return res
end

local function sort_tuples(tuples, index_field_positions)
    local function tuple_comparator(a, b)
        for _, i in ipairs(index_field_positions) do
            if a[i] ~= b[i] then
                if a[i] == nil then
                    return true
                end
                if b[i] == nil then
                    return false
                end
                return a[i] < b[i]
            end
        end

        return false
    end

    table.sort(tuples, tuple_comparator)
end

local function prepare_data(schema, tuples_cnt, sources_cnt, opts)
    local opts = opts or {}
    local use_function_input = opts.use_function_input or false

    local tuples = {}
    local exp_result = {}

    -- Prepare N tables with tuples as input for merger.
    for i = 1, tuples_cnt do
        -- [1, sources_cnt]
        local guava = digest.guava(i, sources_cnt) + 1
        local tuple = schema.gen_tuple(i)
        if tuples[guava] == nil then
            tuples[guava] = {}
        end
        table.insert(tuples[guava], tuple)
        table.insert(exp_result, tuple)
    end

    local index_field_positions = get_index_fields_position(schema.parts)

    -- Sort prepared tuples.
    for _, ts in pairs(tuples) do
        sort_tuples(ts, index_field_positions)
    end

    -- Sort expected output.
    sort_tuples(exp_result, index_field_positions)

    -- Initialize N buffers; write corresponding tuples to that buffers;
    -- that imitates netbox's select with {buffer = ...}.
    local buffers = {}
    local inputs = {}
    for i = 1, sources_cnt do
        inputs[i] = buffer.ibuf()
        msgpackffi.internal.encode_r(inputs[i],
            {[IPROTO_DATA] = tuples[i] or {}}, 0)
        buffers[i] = inputs[i]
    end

    -- Replace buffers[i] with a function that gives one tuple per call.
    if use_function_input then
        for i = 1, sources_cnt do
            local idx = 1
            local received_tuples
            -- XXX: Maybe this func should be an iterator generator?
            inputs[i] = function()
                if received_tuples == nil then
                    local t = msgpackffi.decode(buffers[i].buf)
                    received_tuples = t[IPROTO_DATA]
                end
                local res = received_tuples[idx]
                if res ~= nil then
                    res = box.tuple.new(res)
                end
                idx = idx + 1
                return res
            end
        end
    end

    return inputs, exp_result
end

local function run_merger(test, schema, tuples_cnt, sources_cnt, opts)
    fiber.yield()

    local opts = opts or {}
    local use_function_input = opts.use_function_input or false

    local inputs, exp_result =
        prepare_data(schema, tuples_cnt, sources_cnt, opts)
    local merger_inst = merger.new(schema.parts)

    local res = {}

    -- Merge N inputs into res.
    merger_inst:start(inputs, 1)
    while true do
        local tuple = merger_inst:next()
        if tuple == nil then break end
        table.insert(res, tuple)
    end

    -- prepare for comparing
    for i = 1, #res do
        res[i] = res[i]:totable()
    end

    local use_function_input_str = use_function_input and
        ' (use_function_input)' or ''
    test:is_deeply(res, exp_result,
        ('check order on %3d tuples in %4d sources%s')
        :format(tuples_cnt, sources_cnt, use_function_input_str))
end

local test = tap.test('merger')
test:plan(1 + #schemas * 2 * 6)

local ok, err = pcall(merger.new, {{
    fieldno = 2,
    type = 'unknown',
}})
test:is_deeply({ok, err}, {false, 'Unknown field type: unknown'},
    'incorrect field type')

for _, use_function_input in ipairs({false, true}) do
    for _, schema in ipairs(schemas) do
        local use_function_input_str = use_function_input and
            ' (use_function_input)' or ''
        test:diag('testing on schema %s%s', schema.name, use_function_input_str)

        -- Check with small buffers count.
        local opts = {use_function_input = use_function_input}
        run_merger(test, schema, 100, 1, opts)
        run_merger(test, schema, 100, 2, opts)
        run_merger(test, schema, 100, 3, opts)
        run_merger(test, schema, 100, 4, opts)
        run_merger(test, schema, 100, 5, opts)

        -- Check more buffers then tuples count.
        run_merger(test, schema, 100, 1000, opts)
    end
end

-- XXX: test merger_inst:cmp()

os.exit(test:check() and 0 or 1)
