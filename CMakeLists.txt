cmake_minimum_required(VERSION 3.18)
project(search)
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
option(CXX "enable C++ compilation" ON)
enable_language(CXX)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    message(STATUS "Set up ccache ...")
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ccache)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK ccache)
endif()

add_subdirectory(src)

add_executable(testrun src/test.cpp src/window_size_util.h src/speck_boomerang2.h)
target_link_libraries(testrun absl::numeric  Catch2::Catch2)