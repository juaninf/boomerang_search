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

add_executable(testrun src/test.cpp src/speck_boomerang2.cpp src/ortools_extend_sat.cpp src/bct_entry.cpp src/window_size_util.cpp)
target_link_libraries(testrun absl::numeric Catch2::Catch2 ortools::ortools nlohmann_json::nlohmann_json)