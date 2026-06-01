add_executable(test_formatter test_formatter.cpp)
target_link_libraries(test_formatter PRIVATE
    forall::formatter
    forall::parser
    forall::lexer
    forall::diagnostics
    GTest::gtest_main)
add_test(NAME FormatterTest COMMAND test_formatter)
gtest_discover_tests(test_formatter)
