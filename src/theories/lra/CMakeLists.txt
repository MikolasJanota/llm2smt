add_library(lra STATIC
  rational.cpp
  lra_solver.cpp
)
target_include_directories(lra PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../..)
target_link_libraries(lra PUBLIC sat)
target_compile_features(lra PUBLIC cxx_std_20)
