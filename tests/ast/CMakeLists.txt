add_executable(test_ast test_ast_ops.cpp)
target_link_libraries(test_ast PRIVATE forall::ast GTest::gtest_main)
gtest_discover_tests(test_ast)
