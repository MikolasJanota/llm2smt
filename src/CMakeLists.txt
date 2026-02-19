add_subdirectory(core)
add_subdirectory(sat)
add_subdirectory(theories/euf)
add_subdirectory(parser)

add_executable(llm2smt main.cpp)
target_link_libraries(llm2smt
  PRIVATE
    core
    sat
    euf
    smt_parser
)
target_include_directories(llm2smt PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
