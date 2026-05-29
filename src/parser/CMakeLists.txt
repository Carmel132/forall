add_library(forall_parser)
add_library(forall::parser ALIAS forall_parser)

target_sources(forall_parser
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/parser/parser.hpp
    PRIVATE
        src/parser.cpp
)

# lexer and pretty are PRIVATE: implementation details of parsing.
target_link_libraries(forall_parser
    PUBLIC  forall::compiler_options forall::ast forall::diagnostics
    PRIVATE forall::lexer forall::pretty
)
