#!/usr/bin/env tarantool

local tap = require('tap')
local buffer = require('buffer')
local msgpackffi = require('msgpackffi')
local digest = require('digest')
local merger = require('merger')
local crypto = require('crypto')
local fiber = require('fiber')
local utf8 = require('utf8')

local IPROTO_DATA = 48
local BATCH_SIZE = 10

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
    -- Test index part with 'collation_id' option (as in net.box's
    -- response).
    {
        name = 'collation_id',
        parts = {
            {
                fieldno = 1,
                type = 'string',
                collation_id = 2, -- unicode_ci
            },
        },
        gen_tuple = function(i)
            local letters = {'a', 'b', 'c', 'A', 'B', 'C'}
            if i <= #letters then
                return {letters[i]}
            else
                return {''}
            end
        end,
    },
    -- Test index part with 'collation' option (as in local index
    -- parts).
    {
        name = 'collation',
        parts = {
            {
                fieldno = 1,
                type = 'string',
                collation = 'unicode_ci',
            },
        },
        gen_tuple = function(i)
            local letters = {'a', 'b', 'c', 'A', 'B', 'C'}
            if i <= #letters then
                return {letters[i]}
            else
                return {''}
            end
        end,
    },
}

local function is_unicode_ci_part(part)
    return part.collation_id == 2 or part.collation == 'unicode_ci'
end

local function sort_tuples(tuples, parts)
    local function tuple_comparator(a, b)
        for _, part in ipairs(parts) do
            local fieldno = part.fieldno
            if a[fieldno] ~= b[fieldno] then
                if a[fieldno] == nil then
                    return true
                end
                if b[fieldno] == nil then
                    return false
                end
                if is_unicode_ci_part(part) then
                    return utf8.casecmp(a[fieldno], b[fieldno]) < 0
                end
                return a[fieldno] < b[fieldno]
            end
        end

        return false
    end

    table.sort(tuples, tuple_comparator)
end

local function lowercase_unicode_ci_fields(tuples, parts)
    for i = 1, #tuples do
        local tuple = tuples[i]
        for _, part in ipairs(parts) do
            if is_unicode_ci_part(part) then
                -- Workaround #3709.
                if tuple[part.fieldno]:len() > 0 then
                    tuple[part.fieldno] = utf8.lower(tuple[part.fieldno])
                end
            end
        end
    end
end

local function prepare_data(schema, tuples_cnt, sources_cnt, opts)
    local opts = opts or {}
    local use_function_input = opts.use_function_input or false
    local use_batch_input = opts.use_batch_input or false

    local tuples = {}
    local exp_result = {}

    -- Ensure empty sources are empty table and not nil.
    for i = 1, sources_cnt do
        if tuples[i] == nil then
            tuples[i] = {}
        end
    end

    -- Prepare N tables with tuples as input for merger.
    for i = 1, tuples_cnt do
        -- [1, sources_cnt]
        local guava = digest.guava(i, sources_cnt) + 1
        local tuple = schema.gen_tuple(i)
        table.insert(tuples[guava], tuple)
        table.insert(exp_result, tuple)
    end

    -- Sort prepared tuples.
    for _, ts in pairs(tuples) do
        sort_tuples(ts, schema.parts)
    end

    -- Sort expected output.
    sort_tuples(exp_result, schema.parts)

    -- Wrap tuples from each source into a table to imitate
    -- 'batch request': a request that return multiple select
    -- results. Here we have BATCH_SIZE select results.
    if use_batch_input then
        local new_tuples = {}
        for i = 1, sources_cnt do
            new_tuples[i] = {}
            for j = 1, BATCH_SIZE do
                new_tuples[i][j] = tuples[i]
            end
        end
        tuples = new_tuples
    end

    -- Initialize N buffers; write corresponding tuples to that buffers;
    -- that imitates netbox's select with {buffer = ...}.
    local inputs = {}
    for i = 1, sources_cnt do
        inputs[i] = buffer.ibuf()
        msgpackffi.internal.encode_r(inputs[i], {[IPROTO_DATA] = tuples[i]}, 0)
    end

    -- Replace buffers[i] with a function that gives one tuple per call.
    if use_function_input then
        local buffers = table.copy(inputs)
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

local function input_type_str(opts)
    if opts.use_function_input then
        return ' (use_function_input)'
    elseif opts.use_batch_input then
        return ' (use_batch_input)'
    end

    return ''
end

local function run_merger_internal(context)
    local test = context.test
    local schema = context.schema
    local tuples_cnt = context.tuples_cnt
    local sources_cnt = context.sources_cnt
    local exp_result = context.exp_result
    local merger_inst = context.merger_inst
    local merger_start_opts = context.merger_start_opts
    local opts = context.opts

    local res = {}

    -- Merge N inputs into res.
    merger_inst:start(unpack(merger_start_opts))
    while true do
        local tuple = merger_inst:next()
        if tuple == nil then break end
        table.insert(res, tuple)
    end

    -- Prepare for comparing.
    for i = 1, #res do
        res[i] = res[i]:totable()
    end

    -- unicode_ci does not differentiate btw 'A' and 'a', so the
    -- order is arbitrary. We transform fields with unicode_ci
    -- collation in parts to lower case before comparing.
    lowercase_unicode_ci_fields(res, schema.parts)
    lowercase_unicode_ci_fields(exp_result, schema.parts)

    test:is_deeply(res, exp_result,
        ('check order on %3d tuples in %4d sources%s')
        :format(tuples_cnt, sources_cnt, input_type_str(opts)))
end

local function run_merger(test, schema, tuples_cnt, sources_cnt, opts)
    fiber.yield()

    local opts = opts or {}
    local use_function_input = opts.use_function_input or false
    local use_batch_input = opts.use_batch_input or false

    local inputs, exp_result =
        prepare_data(schema, tuples_cnt, sources_cnt, opts)
    local merger_inst = merger.new(schema.parts)

    local order = 1
    local context = {
        test = test,
        schema = schema,
        tuples_cnt = tuples_cnt,
        sources_cnt = sources_cnt,
        exp_result = exp_result,
        merger_inst = merger_inst,
        merger_start_opts = {inputs, {}},
        opts = opts,
    }

    if use_batch_input then
        test:test('run chained mergers for batch select results', function(test)
            test:plan(BATCH_SIZE)
            context.test = test
            for i = 1, BATCH_SIZE do
                local chain_first = i == 1
                context.merger_start_opts[2].chain_first = chain_first
                -- Use different merger for one of results in the
                -- batch.
                if i == math.floor(BATCH_SIZE / 2) then
                    context.merger_inst = merger.new(schema.parts)
                end
                run_merger_internal(context)
            end
        end)
    else
        run_merger_internal(context)
    end
end

local function run_case(test, schema, opts)
    local opts = opts or {}
    local use_function_input = opts.use_function_input or false
    local use_batch_input = opts.use_batch_input or false

    local case_name = ('testing on schema %s%s'):format(
        schema.name, input_type_str(opts))

    test:test(case_name, function(test)
        test:plan(6)

        -- Check with small buffers count.
        run_merger(test, schema, 100, 1, opts)
        run_merger(test, schema, 100, 2, opts)
        run_merger(test, schema, 100, 3, opts)
        run_merger(test, schema, 100, 4, opts)
        run_merger(test, schema, 100, 5, opts)

        -- Check more buffers then tuples count.
        run_merger(test, schema, 100, 1000, opts)
    end)
end

local test = tap.test('merger')
test:plan(9 + #schemas * 3)

-- Case: pass a field on an unknown type.
local ok, err = pcall(merger.new, {{
    fieldno = 2,
    type = 'unknown',
}})
local exp_err = 'Unknown field type: unknown'
test:is_deeply({ok, err}, {false, exp_err}, 'incorrect field type')

-- Case: try to use collation_id before box.cfg{}.
local ok, err = pcall(merger.new, {{
    fieldno = 1,
    type = 'string',
    collation_id = 2,
}})
local exp_err = 'Cannot use collations: please call box.cfg{}'
test:is_deeply({ok, err}, {false, exp_err},
    'use collation_id before box.cfg{}')

-- Case: try to use collation before box.cfg{}.
local ok, err = pcall(merger.new, {{
    fieldno = 1,
    type = 'string',
    collation = 'unicode_ci',
}})
local exp_err = 'Cannot use collations: please call box.cfg{}'
test:is_deeply({ok, err}, {false, exp_err},
    'use collation before box.cfg{}')

-- For collations.
box.cfg{}

-- Case: try to use both collation_id and collation.
local ok, err = pcall(merger.new, {{
    fieldno = 1,
    type = 'string',
    collation_id = 2,
    collation = 'unicode_ci',
}})
local exp_err = 'Conflicting options: collation_id and collation'
test:is_deeply({ok, err}, {false, exp_err},
    'use collation_id and collation both')

-- Case: unknown collation_id.
local ok, err = pcall(merger.new, {{
    fieldno = 1,
    type = 'string',
    collation_id = 42,
}})
local exp_err = 'Unknown collation_id: 42'
test:is_deeply({ok, err}, {false, exp_err}, 'unknown collation_id')

-- Case: unknown collation name.
local ok, err = pcall(merger.new, {{
    fieldno = 1,
    type = 'string',
    collation = 'unknown',
}})
local exp_err = 'Unknown collation: "unknown"'
test:is_deeply({ok, err}, {false, exp_err}, 'unknown collation name')

local merger_inst = merger.new({{
    fieldno = 1,
    type = 'string',
}})
local start_usage = 'start(merger, {buffer, buffer, ...}' ..
    '[, {descending = <boolean> or <nil>, chain_first = <boolean> or <nil>}])'

-- Case: start() bad opts.
local ok, err = pcall(merger_inst.start, merger_inst, {}, 1)
local exp_err = 'Bad params, use: ' .. start_usage
test:is_deeply({ok, err}, {false, exp_err}, 'start() bad opts')

-- Case: start() bad opts.descending.
local ok, err = pcall(merger_inst.start, merger_inst, {}, {descending = 1})
local exp_err = 'Bad param "descending", use: ' .. start_usage
test:is_deeply({ok, err}, {false, exp_err}, 'start() bad opts.descending')

-- Case: start() bad opts.chain_first.
local ok, err = pcall(merger_inst.start, merger_inst, {}, {chain_first = 1})
local exp_err = 'Bad param "chain_first", use: ' .. start_usage
test:is_deeply({ok, err}, {false, exp_err}, 'start() bad opts.chain_first')

-- Remaining cases.
for _, use_function_input in ipairs({false, true}) do
    for _, use_batch_input in ipairs({false, true}) do
        for _, schema in ipairs(schemas) do
            -- These options are mutually exclusive.
            if use_function_input and use_batch_input then
                goto continue
            end
            local opts = {
                use_function_input = use_function_input,
                use_batch_input = use_batch_input,
            }
            run_case(test, schema, opts)
            ::continue::
        end
    end
end

-- XXX: test merger_inst:cmp()

os.exit(test:check() and 0 or 1)
