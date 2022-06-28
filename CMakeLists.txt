
project(rdiff)
cmake_minimum_required(VERSION 3.2)

set(CMAKE_CXX_STANDARD 17)

add_executable(rdiff rdiff.cpp)

target_compile_options(rdiff PUBLIC -O3 -march=native)
