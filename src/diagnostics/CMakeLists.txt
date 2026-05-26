add_library(forall_diagnostics)
add_library(forall::diagnostics ALIAS forall_diagnostics)

target_sources(forall_diagnostics
    PUBLIC
        FILE_SET HEADERS
        BASE_DIRS include
        FILES
            include/forall/diagnostics/source_location.hpp
            include/forall/diagnostics/diagnostic.hpp
    PRIVATE
        src/diagnostic.cpp
)

target_link_libraries(forall_diagnostics PUBLIC forall::compiler_options)
