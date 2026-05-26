# Shared interface target — every forall library and executable links this.
# Using an INTERFACE library lets us propagate flags transitively without
# imposing them on consumers outside this project.
add_library(forall_compiler_options INTERFACE)
add_library(forall::compiler_options ALIAS forall_compiler_options)

target_compile_features(forall_compiler_options INTERFACE cxx_std_23)

if(FORALL_WARNINGS_AS_ERRORS)
    set(_werror $<IF:$<CXX_COMPILER_ID:MSVC>,/WX,-Werror>)
endif()

target_compile_options(forall_compiler_options INTERFACE
    $<$<CXX_COMPILER_ID:GNU,Clang,AppleClang>:
        -Wall -Wextra -Wpedantic -Wconversion -Wshadow -Wno-unused-parameter
        ${_werror}
    >
    $<$<CXX_COMPILER_ID:MSVC>:
        /W4 /utf-8 /permissive-
        ${_werror}
    >
)
