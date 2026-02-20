add_library(sat cadical_solver.cpp)
target_include_directories(sat PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_compile_features(sat PUBLIC cxx_std_20)
target_link_libraries(sat PUBLIC cadical)
