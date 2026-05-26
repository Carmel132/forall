cmake_minimum_required(VERSION 3.28)
project(forall
    VERSION 0.1.0
    DESCRIPTION "A mathematical proof validation system"
    LANGUAGES CXX
)

# ── Options ───────────────────────────────────────────────────────────────────
option(FORALL_BUILD_TESTS        "Build the test suite"              ON)
option(FORALL_WARNINGS_AS_ERRORS "Treat compiler warnings as errors" OFF)

# ── CMake modules ─────────────────────────────────────────────────────────────
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
include(CompilerOptions)

# Emit compile_commands.json for clangd / IDE tooling
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# ── External dependencies ─────────────────────────────────────────────────────
if(FORALL_BUILD_TESTS)
    include(FetchContent)
    FetchContent_Declare(
        googletest
        GIT_REPOSITORY https://github.com/google/googletest.git
        GIT_TAG        v1.15.2
        GIT_SHALLOW    TRUE
    )
    # Prevent googletest from overriding MSVC CRT settings
    set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(googletest)
    include(CTest)
    include(GoogleTest)
endif()

# ── Sources & tests ────────────────────────────────────────────────────────────
add_subdirectory(src)

if(FORALL_BUILD_TESTS)
    add_subdirectory(tests)
endif()
