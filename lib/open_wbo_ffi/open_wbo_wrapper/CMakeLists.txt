cmake_minimum_required(VERSION 3.24)
project(open_wbo_wrapper)

set(CMAKE_CXX_STANDARD 11)

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang|AppleClang")
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall -Wextra -Wconversion -pedantic -Wfatal-errors -fno-omit-frame-pointer")
    add_link_options(-pthread)
endif ()

include_directories(../open_wbo/include)

add_library(open_wbo_wrapper library.cpp include/library.h)
target_link_libraries(open_wbo_wrapper ${CMAKE_SOURCE_DIR}/../open_wbo/lib/lib_standard.a)