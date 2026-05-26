add_executable(test_kernel test_kernel.cpp)
target_link_libraries(test_kernel PRIVATE forall::kernel GTest::gtest_main)
gtest_discover_tests(test_kernel)
