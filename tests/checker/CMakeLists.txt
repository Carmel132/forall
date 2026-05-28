add_executable(test_checker test_checker.cpp)
target_link_libraries(test_checker PRIVATE forall::checker GTest::gtest_main)
gtest_discover_tests(test_checker)
