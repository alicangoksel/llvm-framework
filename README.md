llvm-framework
==============

LLVM Framework helps to find hazards on multi-threaded programs using LLVM and Math-Sat.

External tools you need:

Clang-LLVM 3.3+
Mathsat 5.2+

* Modify the paths.txt and add your clang and mathsat path. You can modify the existing file to see the format. 

* Sometimes, you might get error while trying to generate the .ll file using the code. The hardcoded part is commented, you can try to use hardcoded version to troubleshoot the problem, if it's related to the Framework code or clang conversion.

Compile the following files and link them (or you can directly use the makefile):

- declarationGenerator.cpp
- globalStore.cpp
- instructionGenerator.cpp
- main.cpp
- mainPartGenerator.cpp
- Utils.cpp

After the compilation, you can run the program with a benchmark file and check the result from MathSAT.

run format: ./\<youroutputfile\> \<benchmarkfile\> \<boundLimit\>

* boundlimit should be an integer and benchmarkfile should be a .c file. You can use the provided benchmarks for testing & initial bug fixing.




