add_library(sat INTERFACE)
target_include_directories(sat INTERFACE ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_compile_features(sat INTERFACE cxx_std_20)
