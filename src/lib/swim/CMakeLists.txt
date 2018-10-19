set(lib_sources
    swim.c
)

set_source_files_compile_flags(${lib_sources})
add_library(swim STATIC ${lib_sources})
