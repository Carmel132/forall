# Build order follows the dependency graph — each module only sees its declared deps.
#
#   diagnostics  (no forall deps)
#       └── ast
#           ├── kernel   ← trusted core; NEVER depends on lexer/parser
#           ├── pretty   ← display utilities; NEVER depends on lexer/parser/kernel
#           └── lexer
#               └── parser  ← links pretty (PRIVATE)
#                   └── checker  ← links pretty (PRIVATE)
#                       └── forall (executable)
#
add_subdirectory(diagnostics)
add_subdirectory(ast)
add_subdirectory(kernel)
add_subdirectory(pretty)
add_subdirectory(lexer)
add_subdirectory(parser)
add_subdirectory(checker)
add_subdirectory(formatter)

add_executable(forall main.cpp)
target_link_libraries(forall PRIVATE forall::checker forall::formatter forall::parser forall::lexer)
set_target_properties(forall PROPERTIES OUTPUT_NAME "forall")

# LSP server (Phase 1: JSON-RPC over stdio, textDocument/publishDiagnostics)
add_executable(forall-lsp lsp/main.cpp)
target_link_libraries(forall-lsp PRIVATE forall::checker forall::parser forall::lexer)
set_target_properties(forall-lsp PROPERTIES OUTPUT_NAME "forall-lsp")

install(TARGETS forall forall-lsp RUNTIME DESTINATION bin)
