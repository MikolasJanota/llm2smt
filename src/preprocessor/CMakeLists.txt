add_library(preprocessor
    simplifier.cpp
    disjunction_bridge.cpp
)
target_include_directories(preprocessor
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/..
)
