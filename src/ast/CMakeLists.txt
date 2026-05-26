add_library(forall_ast)
add_library(forall::ast ALIAS forall_ast)

target_sources(forall_ast
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/ast/node.hpp
    PRIVATE
        src/node.cpp
)

target_link_libraries(forall_ast PUBLIC forall::compiler_options forall::diagnostics)
