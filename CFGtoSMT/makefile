all: llfw
llfw: declarationGenerator.o globalStore.o instructionGenerator.o main.o mainPartGenerator.o Utils.o
	g++ declarationGenerator.o globalStore.o instructionGenerator.o main.o mainPartGenerator.o Utils.o -o llfw
declarationGenerator.o: declarationGenerator.cpp Utils.h
			g++ -c declarationGenerator.cpp
globalStore.o: globalStore.cpp Utils.h
		g++ -c globalStore.cpp
instructionGenerator.o: instructionGenerator.cpp Utils.h
			g++ -c instructionGenerator.cpp
main.o: main.cpp mainPartGenerator.h globalStore.h declarationGenerator.h Utils.h instructionGenerator.h
	g++ -c main.cpp
mainPartGenerator.o: mainPartGenerator.cpp Utils.h
			g++ -c mainPartGenerator.cpp
Utils.o: Utils.cpp
	g++ -c Utils.cpp
