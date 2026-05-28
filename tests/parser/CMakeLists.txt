add_executable(test_parser test_parser.cpp)
# forall::lexer is PRIVATE to forall::parser; the test instantiates Lexer directly.
target_link_libraries(test_parser PRIVATE forall::parser forall::lexer GTest::gtest_main)
gtest_discover_tests(test_parser)
