# Build order follows the dependency graph — each module only sees its declared deps.
#
#   diagnostics  (no forall deps)
#       └── ast
#           ├── kernel   ← trusted core; NEVER depends on lexer/parser
#           └── lexer
#               └── parser
#                   └── checker
#                       └── forall (executable)
#
add_subdirectory(diagnostics)
add_subdirectory(ast)
add_subdirectory(kernel)
add_subdirectory(lexer)
add_subdirectory(parser)
add_subdirectory(checker)

add_executable(forall main.cpp)
target_link_libraries(forall PRIVATE forall::checker)
set_target_properties(forall PROPERTIES OUTPUT_NAME "forall")

install(TARGETS forall RUNTIME DESTINATION bin)
