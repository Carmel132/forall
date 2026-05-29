add_library(forall_checker)
add_library(forall::checker ALIAS forall_checker)

target_sources(forall_checker
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/checker/checker.hpp
    PRIVATE
        src/checker.cpp
)

# kernel, parser, and pretty are PRIVATE: the Checker's public API exposes none of them.
target_link_libraries(forall_checker
    PUBLIC  forall::compiler_options forall::diagnostics
    PRIVATE forall::kernel forall::parser forall::lexer forall::pretty
)
