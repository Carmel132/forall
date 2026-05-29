add_executable(test_pretty test_pretty.cpp)
target_link_libraries(test_pretty PRIVATE forall::pretty GTest::gtest_main)
gtest_discover_tests(test_pretty)
