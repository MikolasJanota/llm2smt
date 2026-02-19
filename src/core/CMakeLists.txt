add_library(core STATIC
  node_manager.cpp
)
target_include_directories(core PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_compile_features(core PUBLIC cxx_std_20)
