cmake_minimum_required(VERSION 3.13)

# Build a small CLI tool to run/print liveness results.
add_executable(jitana-dfa
  main.cpp
)

# Headers live in the top-level include directory.
target_include_directories(jitana-dfa PRIVATE
  ${CMAKE_SOURCE_DIR}/include
)

# Link against the core jitana library/target already defined by the repo.
target_link_libraries(jitana-dfa PRIVATE jitana)

# Emit the binary into build/tools/jitana-dfa/
set_target_properties(jitana-dfa PROPERTIES
  RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tools/jitana-dfa"
)
