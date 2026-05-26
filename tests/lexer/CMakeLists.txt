add_executable(test_lexer test_lexer.cpp)
target_link_libraries(test_lexer PRIVATE forall::lexer GTest::gtest_main)
gtest_discover_tests(test_lexer)
