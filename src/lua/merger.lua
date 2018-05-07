local ffi = require('ffi')
local merger = require('merger')

local merger_t = ffi.typeof('struct merger')

local methods = {
    ['start'] = merger.internal.start,
    ['cmp']   = merger.internal.cmp,
    ['next']  = merger.internal.next,
}

ffi.metatype(merger_t, {
    __index = function(merger, key)
        return methods[key]
    end
})
