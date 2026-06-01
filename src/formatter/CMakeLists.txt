add_library(forall_formatter STATIC src/formatter.cpp)
add_library(forall::formatter ALIAS forall_formatter)

target_include_directories(forall_formatter
    PUBLIC  include
    PRIVATE include)

target_link_libraries(forall_formatter
    PUBLIC  forall::ast
    PRIVATE forall::pretty)

set_target_properties(forall_formatter PROPERTIES
    CXX_STANDARD 23
    CXX_STANDARD_REQUIRED ON)
