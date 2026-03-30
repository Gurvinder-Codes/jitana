cmake_minimum_required(VERSION 2.6)

add_executable(jitana-dfa
    main.cpp
)

target_include_directories(jitana-dfa PRIVATE
    ${CMAKE_SOURCE_DIR}/include
)

target_link_libraries(jitana-dfa PRIVATE jitana)

set_target_properties(jitana-dfa PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/tools/jitana-dfa"
)
