cmake_minimum_required(VERSION 3.5)

add_executable(jitana-ide
    main.cpp
)
target_link_libraries(jitana-ide
    jitana
)

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/output/insn)
