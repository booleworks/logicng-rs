cmake_minimum_required(VERSION 3.24)
project(sharp_sat_wrapper)

set(CMAKE_CXX_STANDARD 11)

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang|AppleClang")
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall -Wextra -Wconversion -pedantic -Wfatal-errors -fno-omit-frame-pointer")
    add_link_options(-pthread)
endif ()

IF(UNIX)
  IF(APPLE)
    IF(CMAKE_APPLE_SILICON_PROCESSOR)
      include_directories(/opt/homebrew/include/Cellar/gmp/6.3.0/include)
    ELSE(CMAKE_APPLE_SILICON_PROCESSOR)
      include_directories(/usr/local/Cellar/gmp/6.3.0/include)
    ENDIF(CMAKE_APPLE_SILICON_PROCESSOR)
  ELSE(APPLE)
    
  ENDIF(APPLE)
ELSE(UNIX)

ENDIF(UNIX)

find_library(GMP_LIB gmp)
find_library(GMPXX_LIB gmpxx)

include_directories(../sharp_sat/include)

add_library(sharp_sat_wrapper library.cpp include/library.h)
target_link_libraries(sharp_sat_wrapper ${CMAKE_SOURCE_DIR}/../sharp_sat/sharpSAT/build/lib_sharp_sat.a ${GMP_LIB} ${GMPXX_LIB})

add_executable(sharp_sat_test main.cpp)
target_link_libraries(sharp_sat_test sharp_sat_wrapper ${CMAKE_SOURCE_DIR}/../sharp_sat/sharpSAT/build/lib_sharp_sat.a ${GMP_LIB} ${GMPXX_LIB})