cmake_minimum_required(VERSION 3.5)
project (SHARPSAT LANGUAGES CXX)

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall -fpie -pie")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS_RELEASE} -O3 -DNDEBUG -fpie -pie")

set(CMAKE_CXX_FLAGS_PROFILING "${CMAKE_CXX_FLAGS_PROFILING} -O3 -g -DNDEBUG -Wall -fpie -pie")

IF(UNIX)
  IF(APPLE)
    include_directories(/usr/local/include)
    include_directories(/opt/local/include)
  ELSE(APPLE)

  ENDIF(APPLE)
ELSE(UNIX)

ENDIF(UNIX)


find_library(GMP_LIB gmp)
find_library(GMPXX_LIB gmpxx)

SET(SHARPSATSRCDIR "logicng-sharp-sat/src")
SET(SOURCES ${SHARPSATSRCDIR}/alt_component_analyzer.cpp ${SHARPSATSRCDIR}/alt_component_analyzer.h
        ${SHARPSATSRCDIR}/component_analyzer.cpp ${SHARPSATSRCDIR}/component_analyzer.h
        ${SHARPSATSRCDIR}/component_cache.cpp ${SHARPSATSRCDIR}/component_cache.h ${SHARPSATSRCDIR}/component_cache-inl.h
        ${SHARPSATSRCDIR}/component_management.cpp ${SHARPSATSRCDIR}/component_management.h
        ${SHARPSATSRCDIR}/instance.cpp ${SHARPSATSRCDIR}/instance.h
        ${SHARPSATSRCDIR}/new_component_analyzer.cpp ${SHARPSATSRCDIR}/new_component_analyzer.h
        ${SHARPSATSRCDIR}/solver.cpp ${SHARPSATSRCDIR}/solver.h
        ${SHARPSATSRCDIR}/statistics.cpp ${SHARPSATSRCDIR}/statistics.cpp
        ${SHARPSATSRCDIR}/containers.h
        ${SHARPSATSRCDIR}/primitive_types.h
        ${SHARPSATSRCDIR}/solver_config.h
        ${SHARPSATSRCDIR}/stack.h
        ${SHARPSATSRCDIR}/stack
        ${SHARPSATSRCDIR}/structures.h
        ${SHARPSATSRCDIR}/containers/binary_heap.h
        ${SHARPSATSRCDIR}/component_types/base_packed_component.cpp
        ${SHARPSATSRCDIR}/component_types/base_packed_component.h
        ${SHARPSATSRCDIR}/component_types/cacheable_component.h
        ${SHARPSATSRCDIR}/component_types/component.h
        ${SHARPSATSRCDIR}/component_types/component_archetype.cpp ${SHARPSATSRCDIR}/component_types/component_archetype.h
        ${SHARPSATSRCDIR}/component_types/difference_packed_component.h
        ${SHARPSATSRCDIR}/component_types/simple_packed_component.h
        ${SHARPSATSRCDIR}/component_types/simple_unpacked_component.h
        ${SHARPSATSRCDIR}/interactive_solver.cpp ${SHARPSATSRCDIR}/interactive_solver.h
)

add_library(_sharp_sat STATIC ${SOURCES})
target_link_libraries(_sharp_sat ${GMP_LIB} ${GMPXX_LIB})
set_target_properties(_sharp_sat PROPERTIES
  CXX_STANDARD 11
  CXX_STANDARD_REQUIRED YES
  CMAKE_POSITION_INDEPENDENT_CODE ON
  CMAKE_BUILD_TYPE Release
)
install(TARGETS _sharp_sat)
