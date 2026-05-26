add_library(forall_lexer)
add_library(forall::lexer ALIAS forall_lexer)

target_sources(forall_lexer
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/lexer/token.hpp
            include/forall/lexer/lexer.hpp
    PRIVATE
        src/lexer.cpp
)

target_link_libraries(forall_lexer PUBLIC forall::compiler_options forall::diagnostics)
