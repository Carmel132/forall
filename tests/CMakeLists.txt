add_subdirectory(ast)
add_subdirectory(kernel)
add_subdirectory(lexer)
add_subdirectory(parser)
add_subdirectory(checker)
add_subdirectory(pretty)
add_subdirectory(formatter)

# End-to-end tests: run the forall binary on the bundled examples and expect
# clean output (exit 0, zero diagnostics).
add_test(NAME e2e_hello_forall
    COMMAND $<TARGET_FILE:forall> "${CMAKE_SOURCE_DIR}/examples/hello.forall"
)
add_test(NAME e2e_keyword_proofs
    COMMAND $<TARGET_FILE:forall> "${CMAKE_SOURCE_DIR}/examples/keyword_proofs.forall"
)
add_test(NAME e2e_stdlib_example
    COMMAND $<TARGET_FILE:forall> "${CMAKE_SOURCE_DIR}/examples/stdlib_example.forall"
)
add_test(NAME e2e_algebra_comm_ring
    COMMAND $<TARGET_FILE:forall>
        --stdlib "${CMAKE_SOURCE_DIR}/stdlib/algebra"
        "${CMAKE_SOURCE_DIR}/stdlib/algebra/comm_ring.forall"
)
