add_library(forall_pretty)
add_library(forall::pretty ALIAS forall_pretty)

target_sources(forall_pretty
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/pretty/to_string.hpp
    PRIVATE
        src/to_string.cpp
)

target_link_libraries(forall_pretty PUBLIC forall::compiler_options forall::ast)
