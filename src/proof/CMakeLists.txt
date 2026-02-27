add_library(proof lean_emitter.cpp proof_minimizer.cpp)
target_include_directories(proof PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..)
target_link_libraries(proof PUBLIC core preprocessor euf cadical)
