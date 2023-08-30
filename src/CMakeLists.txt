cmake_minimum_required(VERSION 3.18)

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

set(CMAKE_CXX_STANDARD 17)
set(COMPILER_FLAGS "-g -O0 -Wall --std=c++17 -march=native -mcpu=apple-m1 -funroll-loops")
#set(LINKER_FLAGS "-static-libstdc++ -static-libgcc")
set(LINKER_FLAGS "-static-libstdc++")
set(CMAKE_CXX_FLAGS "${COMPILER_FLAGS}")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LINKER_FLAGS}")
#set(CMAKE_CXX_CLANG_TIDY clang-tidy-12 -checks='*')

add_subdirectory(poc)
add_subdirectory(3rd)
include_directories(${CMAKE_CURRENT_LIST_DIR}/3rd/or-tools)
include_directories(${CMAKE_CURRENT_LIST_DIR}/3rd/json)
include_directories(${CMAKE_CURRENT_LIST_DIR})


add_library(speck_boomerang speck_boomerang.h speck_boomerang.cpp ortools_extend_sat.cpp bct_entry.cpp window_size_util.cpp util.h util.cpp)
target_link_libraries(speck_boomerang ortools::ortools nlohmann_json::nlohmann_json)

add_executable(experiments experiments.cpp)
target_link_libraries(experiments ortools::ortools nlohmann_json::nlohmann_json speck_boomerang)

add_executable(speck_boomerang_enum speck_boomerang_enum.cpp ortools_extend_sat.cpp bct_entry.cpp window_size_util.cpp util.h util.cpp)
target_link_libraries(speck_boomerang_enum ortools::ortools)

# ==== lea ====
add_executable(lea_boomerang_enum lea_boomerang_enum.cpp ortools_extend_sat.cpp bct_entry.cpp window_size_util.cpp)
target_link_libraries(lea_boomerang_enum ortools::ortools)


add_executable(testrun test.cpp)
target_link_libraries(testrun absl::numeric ortools::ortools nlohmann_json::nlohmann_json Catch2::Catch2WithMain speck_boomerang)
