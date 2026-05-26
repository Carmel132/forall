add_library(forall_kernel)
add_library(forall::kernel ALIAS forall_kernel)

target_sources(forall_kernel
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/kernel/judgment.hpp
            include/forall/kernel/rule.hpp
            include/forall/kernel/kernel.hpp
    PRIVATE
        src/kernel.cpp
)

# The kernel depends ONLY on ast and diagnostics — never on lexer or parser.
# Enforcing this at the CMake level makes trust-boundary violations a build error.
target_link_libraries(forall_kernel PUBLIC forall::compiler_options forall::ast forall::diagnostics)
