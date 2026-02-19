add_library(euf STATIC
  cc.cpp
  flattener.cpp
  euf_solver.cpp
)
target_include_directories(euf PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/../../..)
target_link_libraries(euf PUBLIC core sat)
target_compile_features(euf PUBLIC cxx_std_20)
