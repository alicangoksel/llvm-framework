llvm-framework
==============

LLVM Framework helps to find hazards on multi-threaded programs using LLVM and Math-Sat.

External tools you need:

Clang-LLVM 3.3+
Mathsat 5.2+

1) Modify the paths.txt and add your clang and mathsat path. You can modify the existing file to see the format.
2) Currently, the files to be tested are hardcoded. But the argument version is commented, you can just uncomment it and use with the argument.

Compile the following files and link them:

- declarationGenerator.cpp
- globalStore.cpp
- instructionGenerator.cpp
- main.cpp
- mainPartGenerator.cpp
- Utils.cpp

After the compilation, you can run the program with a benchmark file and check the result from MathSAT.

run format: ./\<youroutputfile\> \<benchmarkfile\> \<boundLimit\>

* boundlimit should be an integer and benchmarkfile should be a .c file. You can use the provided benchmarks for testing & initial bug fixing.




