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
add_test(NAME e2e_algebra_integral_domain
    COMMAND $<TARGET_FILE:forall>
        --stdlib "${CMAKE_SOURCE_DIR}/stdlib/algebra"
        "${CMAKE_SOURCE_DIR}/stdlib/algebra/integral_domain.forall"
)
add_test(NAME e2e_algebra_field
    COMMAND $<TARGET_FILE:forall>
        --stdlib "${CMAKE_SOURCE_DIR}/stdlib/algebra"
        "${CMAKE_SOURCE_DIR}/stdlib/algebra/field.forall"
)
add_test(NAME e2e_algebra_ordered_field
    COMMAND $<TARGET_FILE:forall>
        --stdlib "${CMAKE_SOURCE_DIR}/stdlib/algebra"
        "${CMAKE_SOURCE_DIR}/stdlib/algebra/ordered_field.forall"
)
add_test(NAME e2e_algebra_real
    COMMAND $<TARGET_FILE:forall>
        --stdlib "${CMAKE_SOURCE_DIR}/stdlib/algebra"
        "${CMAKE_SOURCE_DIR}/stdlib/algebra/real.forall"
)
add_test(NAME e2e_analysis_sequence
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/sequence.forall"
)
add_test(NAME e2e_analysis_subsequence
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/subsequence.forall"
)
add_test(NAME e2e_analysis_limits
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/limits.forall"
)
add_test(NAME e2e_analysis_metric_space
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/metric_space.forall"
)

add_test(NAME e2e_analysis_cauchy
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/cauchy.forall"
)

add_test(NAME e2e_analysis_cauchy_real
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/analysis/cauchy_real.forall"
)

add_test(NAME e2e_set_real
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/set_real.forall"
)

add_test(NAME e2e_set_theorems
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/set_theorems.forall"
)

add_test(NAME e2e_nat_theorems
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/nat_theorems.forall"
)

add_test(NAME e2e_int_equiv
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/int_equiv.forall"
)

add_test(NAME e2e_int_construction
    COMMAND $<TARGET_FILE:forall>
        "${CMAKE_SOURCE_DIR}/stdlib/int_construction.forall"
)
