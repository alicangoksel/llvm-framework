//
//  main.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 11/13/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#include <iostream>
#include <map>
#include <set>
#include <vector>
#include <string>
#include <fstream>
#include <cstring>
#include <cstdlib>
#include <sstream>
#include <algorithm>
#include <queue>
#include <stdlib.h>
#include "mainPartGenerator.h"
#include "globalStore.h"
#include "declarationGenerator.h"
#include "Utils.h"
#include "instructionGenerator.h"

using namespace std;

//function prototypes
string exec(const char*);
string initializationPart();
string schedulePart(bool);
string nextStepInactiveThreads();
string nextPcPart(string&);
string nextPcPartTrivial();
string updateToBound(string&);
string generateMainPart(vector<vector<string> >&);
string generateGlobalPart(vector<string>&);
string assertType(vector<string>&);
string mainLastException;
void putGlobalStoreTypes();
void generateAllowedPcMap();


//global variable declarations

string llvmPath;
string mathsatPath;

vector<string> variableDeclarations;
//Thread as key, value = instruction and its possible next program counters.
map<string, vector<pair<string, vector<int> > > > threadInstructionMap;
map<string, map<int, vector<string> > > threadAllowedPcsMap;
map<string, vector<string> > structDefinitions;
set<string> nonMutexStruct;

int bigParanthesisCount = 0;
int smallParanthesisCount = 0;

int stepBound;
int currentStep;
int mainBeginCounter;

bool isMutexPresent;

string currentThread;


int main(int argc, const char * argv[])
{
    
    
    string targetFile = argv[1];
    string stepBoundStr = argv[2];
    //string targetFile = "bigshot_s_true.c";
    string pathFileAddress = "paths.txt";
    
    ifstream ifs(pathFileAddress.c_str());
    if(ifs.is_open()){
        getline(ifs, llvmPath);
        getline(ifs, mathsatPath);
    }
    ifs.close();
    
    string clangCommand = "/clang -c "+targetFile+" -emit-llvm -o "+targetFile+"1";
    string optCommand = "/opt -lowerinvoke -sink -strip-dead-prototypes -simplifycfg -simplify-libcalls -prune-eh -partial-inliner -tailcallelim -mem2reg -lowerswitch -indvars -loops -loop-simplify -loop-unroll -unroll-count=3 -instcombine -globalopt -constmerge -die -argpromotion -instnamer < "+targetFile+"1 > "+targetFile+"2";
    string llvmDisCommand = "/llvm-dis "+targetFile+"2";
    
    system((llvmPath+clangCommand).c_str());
    system((llvmPath+optCommand).c_str());
    system((llvmPath+llvmDisCommand).c_str());
    
    string llvmFile = targetFile+"2.ll";
    cout<<llvmFile<<endl;
    //string llvmFile = "/Users/alicangoksel/Documents/CFGtoSMT/CFGtoSMT/bigshot_s_true.c2.ll";
    //cout<<"Please enter the bound limit: \n";
    //cin>>stepBound;
    stepBound = atoi(stepBoundStr.c_str());
    //string inputFileAddress = "/Users/alicangoksel/Desktop/example_cfg.txt";
    string inputLLVMllFileAddress = llvmFile;
    //ifstream inputFile(inputFileAddress.c_str());
    ifstream inputFile(inputLLVMllFileAddress.c_str());
    vector<string> lines;
    vector<string> globalLines;
    vector<string> failPcs;
    string line;
    string globalPart;
    string start;
    string result;
    string failCondition;
    string nextStepThreadPart;
    bool startedToGetGlobals = false;
    isMutexPresent = false;
    declarationGenerator declGenerator;
    variableDeclarations = declGenerator.initialize();
    //preparing globals reading .ll file.
    if(inputFile.is_open()){
        while(getline(inputFile,line)){
            if(line[0]!='@' && line[0]!='%'){
                if(startedToGetGlobals && line[0]==';'){
                    break;
                }
                else{
                    continue;
                }
            }
            startedToGetGlobals = true;
            globalLines.push_back(line);
        }
    }
    //globalInputFile.close();
    
    //preparing the main and thread parts.
    if(inputFile.is_open()){
        bool isThreadWaitingForPc;
        bool isBlockWaitingForPc;
        bool isFunctionWaitingForPc;
        bool isLastInstructionMalloc;
        pair<string, string> mallocSize;
        string lastThread = "";
        string previousThread;
        string lastBlock;
        string lastFunction;
        vector<string> lines;
        vector<vector<string> > tokenArray;
        vector<vector<string> > mainTokenArray;
        bool ifMain = false;
        bool isThreadActivated = false;
        int pcounter = 1;
        int threadCount = -1;
        int createBound = 0;
        bool ifLastWasMain = false;
        while(getline(inputFile,line)){
            if(line.length()==0){
                continue;
            }
			vector<string> tokens = Utils::split(line);
            tokens.resize(20);
            
            if(tokens[0].length()>0 && tokens[0].compare(";")!=0 && tokens[0].compare("define")!=0 && tokens[0].compare("}")!=0 && tokens[0].compare("declare")!=0 && line.substr(0,2).compare("bb")!=0 && tokens[0].substr(0,1).compare(".")!=0 && tokens[2].compare("preds")!=0) {
                tokens.insert(tokens.begin(), Utils::myToString(pcounter));
                pcounter++;
            }
            
            
            if((tokens[0].compare("define")==0 && tokens[2].substr(1,4).compare("main")==0)){
                ifMain = true;
                threadCount = Utils::threadMap.size();
                continue;
            }
            
            if(tokens[5].substr(0,10).compare("@pthread_mutex_init") == 0 || tokens[5].substr(0,24).compare("@\"\01_pthread_cond_init\"") == 0 || tokens[5].substr(0,15).compare("@pthread_create") == 0){
                ifMain = true;
                mainBeginCounter = createBound;
            }
            
            if(tokens[4].compare("%struct._opaque_pthread_t*,") == 0){
                ifMain = true;
                if(isBlockWaitingForPc){
                    Utils::blockMap.insert(make_pair(lastThread+lastBlock, tokens[0]));;
                    isBlockWaitingForPc = false;
                    mainLastException = tokens[0];
                }
            }
            
            if(ifMain && ((tokens[3].compare("load")==0 && tokens[4].compare("%struct._opaque_pthread_t**") != 0) || (threadCount == 0 && tokens[1].compare("ret")!=0) || (ifMain && tokens[1].compare("store") == 0))){
                ifMain = false;
                if(Utils::threadMap.count("main") == 0){
                    Utils::threadMap.insert(make_pair("main", tokens[0]));
                }
                vector<string> temp;
                temp.push_back("main");
                tokenArray.push_back(temp);
                lastThread = "main";
                ifLastWasMain = true;
            }
            
            if(tokens[5].length()>18 && tokens[5].substr(6,12).compare("pthread_join")==0){
                threadCount--;
            }
            
            //saving main thread tokens in a seperate vector.
            if(ifMain){
                mainTokenArray.push_back(tokens);
                if(tokens[1].compare("ret")==0){
                    break;
                }
            }
            else{
                tokenArray.push_back(tokens);
                
                if(ifLastWasMain){
                    createBound++;
                }
                
                //Saving pc of the last thread.
                if(isThreadWaitingForPc && line.compare("bb:")!=0 && line.substr(0,1).compare(".")!=0 && tokens[2].compare("preds") != 0){
                    Utils::threadMap.insert(make_pair(lastThread, tokens[0]));
                    isThreadWaitingForPc = false;
                    isThreadActivated = true;
                }
                
                if(isFunctionWaitingForPc && line.compare("bb:")!=0 && line.substr(0,1).compare(".")!=0 && tokens[2].compare("preds") != 0){
                    Utils::functionPcMap.insert(make_pair(lastFunction, tokens[0]));
                    isFunctionWaitingForPc = false;
                }
                
                //Saving pc of the last block.
                if(isBlockWaitingForPc){
                    if(!isThreadActivated){
                        Utils::blockMap.insert(make_pair(lastFunction+lastBlock, tokens[0]));
                    }
                    else{
                        Utils::blockMap.insert(make_pair(lastThread+lastBlock, tokens[0]));
                    }
                    isBlockWaitingForPc = false;
                }
                
                if(tokens[0].compare("define")==0 && tokens[2].compare("@main()")!=0 && (tokens[1].compare("i8*")==0 || tokens[2].compare("i8*")==0)){
                    
                    previousThread = lastThread;
                    int threadIndex = -1;
                    if(tokens[1].compare("noalias")==0){
                        threadIndex = 3;
                    }
                    else{
                        threadIndex = 2;
                    }
                    unsigned long pos = tokens[threadIndex].find("(");
                    lastThread = tokens[threadIndex].substr(1,pos-1);
                    isThreadWaitingForPc = true;
                }
                else if(tokens[0].compare("define")==0 && tokens[2].compare("@main()")!=0 && tokens[1].compare("internal")!=0){
                    int threadIndex = -1;
                    if(tokens[1].compare("noalias")==0){
                        threadIndex = 3;
                    }
                    else{
                        threadIndex = 2;
                    }
                    unsigned long pos = tokens[threadIndex].find("(");
                    lastFunction = tokens[threadIndex].substr(1,pos-1);
                    isFunctionWaitingForPc = true;
                    string type = tokens[2];
                    string paramName = tokens[3];
                    string realParam = tokens[3];
                    pos = type.find("(");
                    type = type.substr(pos+1, type.length()-pos);
                    pos = paramName.find(")");
                    if(pos == string::npos){
                        pos = paramName.find(",");
                    }
                    paramName = paramName.substr(1, pos-1);
                    if(type[type.length()-1] != '*'){
                        Utils::variableTypeMap.insert(make_pair(lastFunction+paramName, type));
                    }
                    map<string, string> m;
                    m.insert(make_pair(paramName, "0"));
                    Utils::functionParameterMap.insert(make_pair(lastFunction, m));
                    int counter = 1;
                    int index = threadIndex + 2;
                    while(realParam[realParam.length()-1] != ')'){
                        type = tokens[index];
                        paramName = tokens[index+1].substr(0,tokens[index+1].length()-1);
                        realParam = tokens[index+1];
                        Utils::variableTypeMap.insert(make_pair(lastFunction+paramName,type));
                        Utils::functionParameterMap[lastFunction].insert(make_pair(paramName, Utils::myToString(counter)));
                        counter++;
                        index += 2;
                    }
                }
                else if(line.substr(0,2).compare("bb")==0){
                    size_t pos = line.find(":");
                    lastBlock = "b"+line.substr(0,pos);
                    isBlockWaitingForPc = true;
                }
                else if(line.substr(0,1).compare(".")==0){
                    lastBlock = "b"+tokens[0].substr(0,tokens[0].length()-1);
                    isBlockWaitingForPc = true;
                }
                else if(tokens[2].compare("preds") == 0){
                    lastBlock = "b"+tokens[0].substr(0,tokens[0].length()-1);
                    isBlockWaitingForPc = true;
                }
                else if(tokens[0].compare(";") == 0 && tokens[1].substr(1,5).compare("label")==0){
                    lastBlock = "b"+tokens[1].substr(8);
                    isBlockWaitingForPc = true;
                }
                //Checking store instructions of global variables to use.
                else if(strcmp(tokens[1].c_str(), "store")==0 && tokens[5][0]=='@'){
                    string pc = tokens[0];
                    string globalVar = tokens[5];
                    unsigned long pos = tokens[5].find(",");
                    globalVar = globalVar.substr(1,pos-1);
                    Utils::globalMap[globalVar].push_back(pc);
                    if(isLastInstructionMalloc){
                        Utils::mallocMap.insert(make_pair(globalVar, mallocSize));
                        isLastInstructionMalloc = false;
                        Utils::mallocPcMap.insert(make_pair(Utils::myToString(atoi(pc.c_str())-1),globalVar));
                    }
                }
                //Checking load variables and malloc operations.
                else if(tokens[5].length() > 7 && tokens[5].substr(1,6).compare("malloc")==0){
                    isLastInstructionMalloc = true;
                    mallocSize.first = tokens[5].substr(8);
                    mallocSize.second = tokens[6].substr(0,tokens[6].length()-1);
                }
                else if(tokens[1].compare(("ret"))==0 && lastThread.compare("main")==0){
                    break;
                }
                
                else if(tokens[3].compare("call") == 0 && tokens[4].compare("fastcc")!=0){
                    long pos = tokens[5].find("(");
                    string target = tokens[5].substr(1,pos-1);
                    Utils::returnMap[target] = lastThread+Utils::insertTemp(tokens[1]).substr(1);
                    if(Utils::functionPcMap.count(target) > 0){
                        if(Utils::threadFunctionMap.count(lastThread) == 0){
                            set<string> s;
                            s.insert(target);
                            Utils::threadFunctionMap[lastThread] = s;
                        }
                        else{
                            Utils::threadFunctionMap[lastThread].insert(target);
                        }
                        
                        
                        int funcIndex = -1;
                        if(tokens[4][0] == '@'){
                            funcIndex = 4;
                        }
                        else{
                            funcIndex = 5;
                        }
                        pos = tokens[funcIndex].find("(");
                        string func = tokens[funcIndex].substr(1,pos-1);
                        string functarget = Utils::insertTemp(tokens[1]).substr(1);
                        string realParam = tokens[funcIndex+1];
                        int counter = 0;
                        for(int i=funcIndex;;i += 2){
                            realParam = tokens[i+1];
                            if(tokens[i][tokens[i].length()-1] == '*'){
                                int index = (i-funcIndex)/2;
                                string pointerTarget = tokens[i+1];
                                pointerTarget = pointerTarget.substr(1,pointerTarget.length()-2);
                                map<string, string>::iterator itr;
                                map<string, string> paramMap = Utils::functionParameterMap[func];
                                for(itr = paramMap.begin(); itr != paramMap.end(); ++itr){
                                    if(itr->second.compare(Utils::myToString(index)) == 0){
                                        Utils::functionParameterMap[func][itr->first] = pointerTarget;
                                        break;
                                    }
                                }
                            }
                            else{
                                int index = (i-funcIndex)/2;
                                map<string, string>::iterator itr;
                                map<string, string> paramMap = Utils::functionParameterMap[func];
                                for(itr = paramMap.begin(); itr != paramMap.end(); ++itr){
                                    if(itr->second.compare(Utils::myToString(index)) == 0){
                                        break;
                                    }
                                }
                                string param = tokens[i+1];
                                long pos = param.find(")");
                                if(pos == string::npos){
                                    pos = param.find(",");
                                }
                                param = param.substr(0,pos);
                                param = param.substr(1);
                                counter++;
                            }
                            
                            if(realParam[realParam.length()-1] == ')'){
                                break;
                            }
                            
                        }
                        
                    }
                }
                
            }
        }
        
        globalPart = generateGlobalPart(globalLines);
        globalPart = "\n; Global variable initialization part\n" + globalPart;
        currentStep = 0;
        Utils::blockMap.size();
        if(!Utils::mutexSet.empty()){
            isMutexPresent = true;
        }
        
        vector<string> globals = declGenerator.execute(Utils::globalMap, Utils::threadMap, Utils::mutexSet, Utils::condVarSet, Utils::mallocMap, stepBound);
        variableDeclarations.insert(variableDeclarations.end(), globals.begin(), globals.end());
        
        //Generating main part using another class.
        string mainPart = generateMainPart(mainTokenArray);
        mainPart = "\n; Main thread part.\n" + mainPart;
        //Creating variable initialization part.
        start = "\n; Variable initialization part.\n"+initializationPart()+"\n";
        //Creating scheduling part.
        start += "\n; Scheduling part\n"+schedulePart(true)+"\n";
        start += "\n; Transition part.\n";
        start += "\n; *** Bound step = 1 ***";
        
        instructionGenerator insGenerator;
        insGenerator.setCurrentStep(currentStep);
        
        nextStepThreadPart = nextStepInactiveThreads();
        //result += nextStepThreadPart;
        int instructionCounter = 1;
        bool fastccMode = false;
        for(int i=0;i<tokenArray.size();i++){
            

            vector<string> currentTokens = tokenArray[i];
            string currentInstruction = ""; //Eskiden newline di.
            currentTokens.resize(20);
            if(currentTokens[0].compare("define")==0 && currentTokens[2].compare("fastcc") != 0){
                int threadIndex = -1;
                if(currentTokens[1].compare("noalias")==0){
                    threadIndex = 3;
                }
                else{
                    threadIndex = 2;
                }
                string temp = currentTokens[threadIndex];
                size_t pos = temp.find("(");
                temp = temp.substr(1,pos-1);
                currentThread = temp;
                threadInstructionMap[currentThread].resize(32);
                instructionCounter = 1;
                insGenerator.setCurrentThread(currentThread);
                fastccMode = false;
                //result += "\n; *** Thread "+currentThread+" ***";
            }
            else if(currentThread.length() == 0){
                continue;
            }
            else if(currentTokens[0].compare("main") == 0){
                currentThread = "main";
                threadInstructionMap[currentThread].resize(32);
                instructionCounter = 1;
                insGenerator.setCurrentThread(currentThread);
                fastccMode = false;
            }
            else if(fastccMode){
                continue;
            }
            else if(currentTokens[2].compare("fastcc") == 0){
                fastccMode = true;
                continue;
            }
            //These labels do not have instructions, so we can skip.
            else if(currentTokens[0].size() == 0 || currentTokens[0].compare(";")==0 || currentTokens[0].substr(0,1).compare(".") == 0 || currentTokens[0].compare("bb") == 0
                    || currentTokens[0].compare("declare") == 0 || currentTokens[0].compare("codeRepl.i:") == 0 ||
                    currentTokens[2].compare("preds") == 0){
                continue;
            }
            else{
                
                //result += "\n";
                //                if(i != tokenArray.size()-1){
                //                    currentInstruction += " (or";
                //                }
                
                if(currentTokens[4].substr(0,9).compare("@__assert")==0 || currentTokens[3].compare("%.preheader")==0){
                    failPcs.push_back(currentTokens[0]);
                    //cout<<failCondition<<endl;
                }
                else if(currentTokens[5].compare("%.preheader,")==0 || currentTokens[7].compare("%.preheader")==0){
                    failPcs.push_back(Utils::blockMap[currentThread+"b.preheader"]);
                }
                else if(currentTokens[7].compare("%codeRepl.i")==0){
                    failPcs.push_back(Utils::blockMap["mainbcodeRepl.i"]);
                }
                
                currentInstruction += insGenerator.convert(currentTokens);
                
                vector<int> nextPc;
                smallParanthesisCount++;
                //Setting next program counter depends on instructions.
                if(currentTokens[1].compare("br") != 0 && currentTokens[1].compare("ret") !=0
                   && currentTokens[1].compare("unreachable") != 0)
                {
                    
                    int pc = atoi(currentTokens[0].c_str())+1;
                    if(currentThread.compare("main") == 0 && (i+1) != tokenArray.size() && tokenArray[i+1][0].compare("main") == 0){
                        pc = atoi(tokenArray[i+2][0].c_str());
                    }
                    
                    string pc2 = Utils::myToString(pc);
                    currentInstruction += nextPcPart(pc2);
                    
                    nextPc.push_back(atoi(pc2.data()));
                    
                }
                else if(currentTokens[1].compare("br")==0){
                    if(currentTokens[2].compare("i1")!=0){
                        
                        nextPc.push_back(atoi(Utils::blockMap[currentThread+"b"+currentTokens[3].substr(1)].data()));
                        
                    }
                    else{
                        
                        size_t comma = currentTokens[7].find(",");
                        if(comma==string::npos){
                            comma = currentTokens[7].length();
                        }
                        nextPc.push_back(atoi(Utils::blockMap[currentThread+"b"+currentTokens[5].substr(1,currentTokens[5].size()-2)].data()));
                        nextPc.push_back(atoi(Utils::blockMap[currentThread+"b"+currentTokens[7].substr(1,comma-1)].data()));
                        
                    }
                }
                // Bu eski .ll file da 6 ydi, 5 e cevirdik, noalias parametresinden kaynaklaniyor olabilir.
                if(currentTokens[5].length()>17 && currentTokens[5].substr(6,17).compare("pthread_cond_wait")==0){
                    Utils::condVariableThreadMap.insert(make_pair(currentThread, currentTokens[6].substr(1,currentTokens[6].length()-2)));
                }
                
                threadInstructionMap[currentThread][atoi(currentTokens[0].data())-atoi(Utils::threadMap[currentThread].data())] = make_pair(currentInstruction, nextPc);
                ++instructionCounter;
                //result += currentInstruction;
                
            }
        }
        
        //        for(int i=0;i<smallParanthesisCount;i++){
        //            result += ")";
        //        }
        
        //Other steps will have the same instructions. Only counters will increase by one so no need to reconstruct whole code.
        result += nextStepThreadPart;
        
        //Initial paranthesis count is 2. One from connecting and in the scheduling part and other for nextstepthread program counter control.
        smallParanthesisCount = 1+Utils::threadMap.size()+Utils::functionPcMap.size();
        map<string, vector<pair<string, vector<int> > > >::iterator endPtr = threadInstructionMap.end();
        endPtr--;
        for(map<string, vector<pair<string, vector<int> > > >::iterator itr = threadInstructionMap.begin(); itr != threadInstructionMap.end(); ++itr){
            if(itr == endPtr){
                result += "\n"+itr->second[0].first;
            }
            else
            {
                result += "\n(or"+itr->second[0].first;
                smallParanthesisCount++;
            }
        }
        for(int i=0;i<smallParanthesisCount;i++){
            result += ")";
        }
        
        generateAllowedPcMap();
        
        //Default and ve or lar sikinti cikartiyo dikkat etmek lazim.
        for(int i=1;i<stepBound;i++){
            currentStep++;
            smallParanthesisCount = 1+Utils::threadMap.size()+Utils::functionPcMap.size();
            insGenerator.setCurrentStep(currentStep);
            result += "\n; *** Bound step"+Utils::myToString(currentStep+1)+" ***\n";
            string currentStep = nextStepThreadPart;
            string newResult = currentStep;
            map<string, map<int, vector<string> > >::iterator endPointer = threadAllowedPcsMap.end();
            --endPointer;
            map<string, string> temp = Utils::threadMap;
            for(map<string, string> ::iterator itr = Utils::functionPcMap.begin(); itr!= Utils::functionPcMap.end(); ++itr){
                temp[itr->first] = itr->second;
            }
            for(map<string, map<int, vector<string> > >::iterator itr = threadAllowedPcsMap.begin(); itr != threadAllowedPcsMap.end(); ++itr){
                //for i<= e kadar, map ten allowed pc leri, ordan da instruction lari al ekle. ith stepe kadar olan instructionlari aliyoruz.
                string chosenThread = itr->first;
                int counter = 0;
                int limit = std::min(i+1,(int)threadAllowedPcsMap[chosenThread].size()-1);
                for(int j=0;j<limit;j++){
                    vector<string> allowedPcs = threadAllowedPcsMap[chosenThread][j];
                    for(int m=0;m<allowedPcs.size();m++){
                        if(itr == endPointer && j+1 == limit && m+1 == allowedPcs.size()){
                            newResult += "\n"+threadInstructionMap[chosenThread][atoi(allowedPcs[m].data())-atoi(temp[chosenThread].data())].first;
                        }
                        else{
                            newResult += "\n(or"+threadInstructionMap[chosenThread][atoi(allowedPcs[m].data())-atoi(temp[chosenThread].data())].first;
                            smallParanthesisCount++;
                        }
                    }
                }
            }
            newResult = updateToBound(newResult);
            newResult = schedulePart(false)+newResult;
            for(int j=0;j<smallParanthesisCount;j++){
                newResult += ")";
            }
            //cout<<newResult<<endl;
            result += newResult;
        }
        
        for(int i=0;i<stepBound-1;i++){
            result += ")";
        }
        
        failCondition = assertType(failPcs);
        result += "\n; *** Fail Condition ***\n"+failCondition;
        for(int i=0;i<bigParanthesisCount;i++){
            result += ")";
        }
        
        result = start + result;
        result = mainPart + "\n" + result;
        result = globalPart + "\n" + result;
        
    }
	else{
		cout<<"Unable to open the file"<<endl;
	}
    
    inputFile.close();
    //Creating global variable definitions for store operations (x0,i0 etc.)
    putGlobalStoreTypes();
    vector<string> localDeclarations = declGenerator.execute(Utils::variableTypeMap);
    variableDeclarations.insert(variableDeclarations.end(), localDeclarations.begin(), localDeclarations.end());
    
    for(int i=variableDeclarations.size()-1;i>=0;i--){
        result = variableDeclarations[i] + "\n"+result;
    }
    result += "\n(check-sat)";
    result += "\n(exit)";
    
    Utils::replaceiWithI(result);
    
    ofstream output;
    string outputFile = targetFile+".smt2";
    output.open(outputFile.data());
    output<<result;
    output.close();
    string mathsatCommand = mathsatPath+"/mathsat -input=smt2 < "+outputFile;
    string mathSatResult = exec(mathsatCommand.c_str());
    cout<<mathSatResult;
    return 0;
}

/*
 * Function to get terminal output from mathsat result.
 */
string exec(const char* cmd) {
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return "ERROR";
    char buffer[128];
    std::string result = "";
    while(!feof(pipe)) {
    	if(fgets(buffer, 128, pipe) != NULL)
    		result += buffer;
    }
    pclose(pipe);
    return result;
}

/*
 * Initializing global variables at the start of transition relation.
 */
string initializationPart(){
    string result = "(assert (and ";
    bigParanthesisCount += 2;
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    for(int i=0;i<temp.size()-1;i++){
        result += " (and";
    }
    
    map<string, string>::iterator itr;
    
    for(itr=temp.begin();itr!=temp.end();itr++){
        result += " (= " + itr->first + "pc0 (_ bv"+itr->second+" 32))";
        if(itr != temp.begin()){
            result += ")";
        }
    }
    
    result += " (and";
    bigParanthesisCount++;
    
    for(int i=0;i<Utils::globalMap.size()-1;i++){
        result += " (and";
    }
    
    map<string, vector<string> >::iterator itr2;
    for(itr2=Utils::globalMap.begin();itr2!=Utils::globalMap.end();itr2++){
        
        result += " (= "+itr2->first+"_0 "+itr2->first+")";
        
        if(itr2!= Utils::globalMap.begin()){
            result += ")";
        }
    }
    
    return result;
}

/*
 * Creating scheduling part for each bound.
 */
string schedulePart(bool isFirst){
    if(isFirst){
        mainBeginCounter--;
    }
    string result = " (and";
    //smallParanthesisCount++;
    if(isFirst){
        bigParanthesisCount++;
        for(int i=0; i<stepBound;i++){
            result += " (and";
        }
    }
    
    if(!isFirst && mainBeginCounter>0){
        isFirst = true;
        mainBeginCounter--;
    }
    
    for(int i=0;i<Utils::threadMap.size()-1;i++){
        result += " (or";
    }
    for(int i=0;i<Utils::functionPcMap.size();i++){
        result += " (or";
    }
    
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    map<string, string>::iterator itr;
    map<string, string>::iterator itr2;
    for(itr = temp.begin();itr!=temp.end();++itr){
        bool isCondVar = false;
        bool isThereFuction = false;
        bool isMain = false;
        bool isCall = false;
        if(!isFirst && Utils::condVarSet.size()>0 && Utils::condVariableThreadMap.count(itr->first)>0){
            result += " (and (not "+Utils::condVariableThreadMap[itr->first]+Utils::myToString(currentStep)+")";
            isCondVar = true;
        }
        int relatedParanthesisCount = 0;
        if(Utils::threadFunctionMap.count(itr->first) > 0){
            set<string> relatedFunctions = Utils::threadFunctionMap[itr->first];
            for(set<string>::iterator itr2 = relatedFunctions.begin();itr2 != relatedFunctions.end(); ++itr2){
                result += " (and (not call_"+*itr2+Utils::myToString(currentStep)+")";
                relatedParanthesisCount++;
                isThereFuction = true;
            }
        }
        if(Utils::functionPcMap.count(itr->first) > 0){
            result += " (and call_"+itr->first+Utils::myToString(currentStep);
            isCall = true;
        }
        for(int j=0; j< temp.size()-1;j++){
            result += " (and";
        }
        if(itr->first.compare("main")==0 && !isFirst){
            isMain = true;
            for(int j=0;j<Utils::threadMap.size()-1;j++){
                result += " (and";
            }
            bool firstElement = true;
            for(itr2 = Utils::threadMap.begin();itr2 != Utils::threadMap.end(); ++itr2){
                if(itr2->first.compare("main") == 0){
                    continue;
                }
                result += " (bvsge "+itr2->first+"pc"+Utils::myToString(currentStep-1);
                result += " (_ bv"+Utils::myToString(Utils::threadLastPcMap[itr2->first])+" 32))";
                if(!firstElement){
                    result += ")";
                }
                firstElement = false;
            }
        }
        result += " "+itr->first;
        
        result += Utils::myToString(currentStep);
        if(isMain){
            result += ")";
        }
        for(itr2 = temp.begin();itr2 != temp.end(); ++itr2){
            if(itr->first.compare(itr2->first)!=0){
                result += " (not "+itr2->first+Utils::myToString(currentStep)+"))";
            }
        }
        if(itr!=temp.begin()){
            result += ")";
        }
        if(isCondVar){
            result += ")";
        }
        if(isThereFuction){
            result += ")";
        }
        if(isCall){
            result += ")";
        }
        for(int i=0;i<relatedParanthesisCount-1;i++){
            result += ")";
        }
        relatedParanthesisCount = 0;
    }
    
    return result;
}

/*
 * Conversion of assert type instruction.
 */
string assertType(vector<string>& pcs){
    //Last part shoudln't have or, so holding a counter and limit.
    string result = "";
    int limit = stepBound * Utils::threadMap.size()-1;
    int counter = 0;
    map<string, string>::iterator itr;
    for(int i=0;i<stepBound;i++){
        for(itr = Utils::threadMap.begin(); itr!=Utils::threadMap.end(); ++itr){
            result += " (or";
            int smallCounter = 0;
            for(int j=0;j<pcs.size();j++){
                if(j+1 != pcs.size()){
                    result += " (or";
                    smallCounter++;
                }
                result += "(= "+itr->first+"pc"+Utils::myToString(i);
                result += " (_ bv"+pcs[j]+" 32))";
             }
            for(int j=0;j<smallCounter;j++){
                result += ")";
            }
            counter++;
            if(counter == limit){
                break;
            }
        }
    }
    itr = Utils::threadMap.end();
    int smallCounter = 0;
    for(int j=0;j<pcs.size();j++){
        if(j+1 != pcs.size()){
            result += " (or";
            smallCounter++;
        }

        result += " (= "+(--itr)->first+"pc"+Utils::myToString(stepBound-1);
        result += " (_ bv"+pcs[j]+" 32))";
    }
    
    for(int j=0;j<smallCounter;j++){
        result += ")";
    }
    for(int i=0;i<limit;i++){
        result += ")";
    }
    
    //cout<<result<<endl;
    return result;
}

/*
 * Next pc assignment of inactive threads.
 */
string nextStepInactiveThreads(){
    
    string result = "";
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    for(map<string, string>::iterator itr = temp.begin(); itr != temp.end(); ++itr){
        result += "\n(and";
        smallParanthesisCount++;
        result += " (or";
        result += " (and (not "+itr->first+Utils::myToString(currentStep)+")";
        result += " (= "+itr->first+"pc"+Utils::myToString(currentStep+1)+" "+itr->first+"pc"+Utils::myToString(currentStep);
        result += "))";
        result += " (and "+itr->first+Utils::myToString(currentStep);
        result += " true))";
    }
    return result;
}


/*
 * Jumps current thread's program counter and inactive threads' pc's remain the same.
 */
string nextPcPart(string& pc){
    string result = "";
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    map<string, string>::iterator itr;
    for(itr = temp.begin(); itr!= temp.end(); ++itr){
        if(itr->first.compare(currentThread)==0){
            result += " (= "+itr->first+"pc"+Utils::myToString(currentStep+1)+" (_ bv"+pc+" 32)))";
        }
    }
    
    //cout<<result<<endl;
    return result;
}

/*
 * Increments current thread's program counter by one and inactive threads' pc's remain the same.
 */
string nextPcPartTrivial(){
    string result = "";
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    map<string, string>::iterator itr;
    for(itr = temp.begin(); itr!= temp.end(); ++itr){
        if(itr->first.compare(currentThread)!=0){
            result += " (= "+itr->first+"pc"+Utils::myToString(currentStep+1)+" "+itr->first+"pc"+Utils::myToString(currentStep)+"))";
        }
    }
    
    //cout<<result<<endl;
    return result;
}

/*
 * Updates the given instructions to the given bound.
 */
string updateToBound(string& newResult){
    
    map<string, string>::iterator itr;
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    for(itr = temp.begin();itr!=temp.end();++itr){
        string target = " "+itr->first+Utils::myToString(1)+" ";
        string replacement = " "+itr->first+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = " "+itr->first+Utils::myToString(1)+")";
        replacement = " "+itr->first+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = " "+itr->first+Utils::myToString(0)+" ";
        replacement = " "+itr->first+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = " "+itr->first+Utils::myToString(0)+")";
        replacement = " "+itr->first+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(1)+" ";
        replacement = itr->first+"pc"+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(1)+")";
        replacement = itr->first+"pc"+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(0)+")";
        replacement = itr->first+"pc"+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(0)+" ";
        replacement = itr->first+"pc"+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(-1)+")";
        replacement = itr->first+"pc"+Utils::myToString(currentStep-1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr->first+"pc"+Utils::myToString(-1)+" ";
        replacement = itr->first+"pc"+Utils::myToString(currentStep-1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
    }
    map<string, vector<string> >::iterator itr2;
    for(itr2 = Utils::globalMap.begin();itr2!=Utils::globalMap.end();++itr2){
        string target = itr2->first+"_"+Utils::myToString(1)+" ";
        string replacement = itr2->first+"_"+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr2->first+"_"+Utils::myToString(1)+")";
        replacement = itr2->first+"_"+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr2->first+"_"+Utils::myToString(0)+" ";
        replacement = itr2->first+"_"+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = itr2->first+"_"+Utils::myToString(0)+")";
        replacement = itr2->first+"_"+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
    }
    set<string>::iterator itr3;
    for(itr3 = Utils::mutexSet.begin(); itr3!=Utils::mutexSet.end(); ++itr3){
        string currentMutex = " "+*itr3;
        string target = currentMutex+Utils::myToString(1)+" ";
        string replacement = currentMutex+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = currentMutex+Utils::myToString(1)+")";
        replacement = currentMutex+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        
        target = currentMutex+Utils::myToString(0)+" ";
        replacement = currentMutex+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = currentMutex+Utils::myToString(0)+")";
        replacement = currentMutex+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        
    }
    
    set<string>::iterator itr4;
    for(itr4 = Utils::condVarSet.begin(); itr4!=Utils::condVarSet.end(); ++itr4){
        string condVar = " "+*itr4;
        string target = condVar+Utils::myToString(1)+" ";
        string replacement = condVar+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = condVar+Utils::myToString(1)+")";
        replacement = condVar+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = condVar+Utils::myToString(0)+" ";
        replacement = condVar+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = condVar+Utils::myToString(0)+")";
        replacement = condVar+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
    }
    
    map<string, pair<string, string> >::iterator itr5;
    for(itr5 = Utils::mallocMap.begin(); itr5 != Utils::mallocMap.end(); ++itr5){
        string initDecl = " init"+itr5->first;
        //Simdilik i8 yapiyoruz, malloc llvm de i64 olarak cevrilmis sikinti var.
        string targetDecl = " target"+itr5->first;
        string target = initDecl+Utils::myToString(1)+" ";
        string replacement = initDecl+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = initDecl+Utils::myToString(1)+")";
        replacement = initDecl+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = initDecl+Utils::myToString(0)+" ";
        replacement = initDecl+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = initDecl+Utils::myToString(0)+")";
        replacement = initDecl+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = targetDecl+Utils::myToString(1)+" ";
        replacement = targetDecl+Utils::myToString(currentStep+1)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = targetDecl+Utils::myToString(1)+")";
        replacement = targetDecl+Utils::myToString(currentStep+1)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        target = targetDecl+Utils::myToString(0)+" ";
        replacement = targetDecl+Utils::myToString(currentStep)+" ";
        Utils::myReplaceAll(newResult, target, replacement);
        target = targetDecl+Utils::myToString(0)+")";
        replacement = targetDecl+Utils::myToString(currentStep)+")";
        Utils::myReplaceAll(newResult, target, replacement);
        
    }
    
    return newResult;
    
}

/*
 * Creates the main part of the program.
 * Creates a MainPartGenerator object and uses its functions to generate instructions.
 */
string generateMainPart(vector<vector<string> >& mainTokenArray){
    
    string result = "(assert";
    int paranthesisCount = 1;
    mainPartGenerator generator;
    int counter = 0;
    for(int i=0;i<mainTokenArray.size();i++){
        vector<string> tokens = mainTokenArray[i];
        tokens.resize(20);
        if(tokens[0].compare("thread")==0 || tokens[1].compare("ret")==0 || tokens[0].compare("block")==0 || tokens[0].length() == 0){
            continue;
        }
        
        Utils::variableTypeMap.insert(make_pair("pc"+Utils::myToString(counter), "I32"));
        ++counter;
        bool isStore = false;
        string currentTerm = "";
        if(i != mainTokenArray.size()-2){
            currentTerm += " (and";
            paranthesisCount++;
        }
        currentTerm += generator.pcType(tokens[0]);
        
        if(tokens[3].compare("alloca")==0){
            string var = "main"+tokens[1].substr(1);
            string type = "";
            if(tokens[4].compare("%struct._opaque_pthread_t*,")==0){
                type = "I64";
            }
            else{
                type = tokens[4].substr(0,tokens[4].length()-1);
            }
            Utils::variableTypeMap.insert(make_pair(var, type));
        }
        else if(tokens[1].compare("store")==0){
            currentTerm = " (and" + currentTerm;
            currentTerm += generator.storeType(tokens[3], tokens[5]);
            if(tokens[5][0] == '@'){
                isStore = true;
            }
            currentTerm += ")";
        }
        else if(tokens[3].compare("bitcast")==0){
            string var = "main"+Utils::insertTemp(tokens[1]).substr(1);
            string type = tokens[7].substr(0,tokens[7].length()-1);
            Utils::variableTypeMap.insert(make_pair(var, type));
            currentTerm = " (and"+currentTerm;
            currentTerm += generator.bitcastType(tokens[1], tokens[4], tokens[5], tokens[7]);
            currentTerm += ")";
        }
        else if(tokens[3].compare("call")==0 && tokens[5].substr(0,15).compare("@pthread_create")==0){
            bool isGlobal = false;
            string var = tokens[11].substr(1,tokens[11].length()-2)+"arg";
            string type = tokens[9].substr(0,tokens[9].length()-1);
            Utils::variableTypeMap.insert(make_pair(var, type));
            //currentTerm = " (and"+currentTerm;
            string threadName = tokens[11].substr(1,tokens[11].length()-2);
            string targetName = tokens[13].substr(0,tokens[13].length()-1);
            if(targetName.compare("bitcas") == 0){
                targetName = tokens[15] + "_0";
                isGlobal = true;
            }
            if(targetName.compare("null")!=0){
                //currentTerm += generator.callType(threadName, targetName, isGlobal);
            }
            //currentTerm += ")";
        }
        
        if(tokens[3].compare("call")==0 && tokens[4].compare("fastcc") != 0){
            string var = "main"+Utils::insertTemp(tokens[1]).substr(1);
            string type = tokens[4];
            Utils::variableTypeMap.insert(make_pair(var, type));
        }
        
        if(isStore){
            //currentTerm = " (and"+currentTerm;
            string globalVar = tokens[5].substr(1);
            pair<string, string> result = generator.globalStoreModifier(globalVar, tokens[0]);
            //currentTerm += result.first;
            //currentTerm += ")";
            Utils::initialValueMap.insert(make_pair(tokens[5].substr(1), result.second));
            Utils::variableTypeMap.insert(make_pair(result.second, "I32"));
            Utils::globalMap[globalVar].push_back(tokens[0]);
            Utils::globalStoreCount[globalVar]++;
        }
        
        result += currentTerm;
    }
    
    for(int j=0;j<paranthesisCount;j++){
        result += ")";
    }
    
    //cout<<result<<endl;
    return result;
    
}

/*
 * Creates the global initialization part of the program.
 * Creates a GlobalStore object and uses its functions to generate instructions.
 */
string generateGlobalPart(vector<string>& lines){
    string result = "(assert";
    vector<string> storeInstructions;
    int paranthesisCount = 1;
    globalStoreGenerator gs;
    for(int i=0;i<lines.size();i++){
        string line = lines[i];
        size_t firstPosition = 0;
        size_t lastPosition = line.find_first_of(" ");
        vector<string> tokens;
        while(lastPosition != string::npos){
            string temp = line.substr(firstPosition,lastPosition-firstPosition);
            if(strcmp(temp.c_str(),"c") == 0){
                break;
            }
            
            tokens.push_back(temp);
            
            firstPosition = lastPosition+1;
            lastPosition = line.find_first_of(" ",firstPosition);
            if(lastPosition == string::npos){
                tokens.push_back(line.substr(firstPosition));
            }
        }
        
        if(tokens[0].compare("%struct._opaque_pthread_attr_t")==0 ||
           tokens[0].compare("%union.pthread_attr_t")==0 ||
           tokens[0].compare("struct._opaque_pthread_mutexattr_t")==0 ||
           tokens[0].compare("%struct._opaque_pthread_condattr_t")==0)
        {
            string decl1 = "(define-sort Array";
            string tempType = tokens[5].substr(1)+tokens[7].substr(0,tokens[7].length()-1);
            decl1 += tempType;
            decl1 += " () (Array (_ BitVec ";
            decl1 += Utils::findLog(atoi((tokens[5].substr(1)).c_str()));
            decl1 += ") "+tokens[7].substr(0,tokens[7].length()-1)+"))";
            if(Utils::defineSet.count(tempType) == 0){
                variableDeclarations.push_back(decl1);
                Utils::defineSet.insert(tempType);
            }
            string decl2 = "(define-sort "+tokens[0].substr(1);
            decl2 += "() (Pair "+tokens[4].substr(0,tokens[4].length()-1);
            decl2 += " Array"+tempType+"))";
            variableDeclarations.push_back(decl2);
            
        }
        else if(tokens[0].compare("%union.pthread_mutex_t")==0 ||
                tokens[0].compare("%struct.__pthread_mutex_s")==0 ||
                tokens[0].compare("%struct.__pthread_internal_list")==0 ||
                tokens[0].compare("%struct._opaque_pthread_mutex_t")==0 ||
                tokens[0].compare("%struct._opaque_pthread_cond_t")==0){
            string decl = "(define-sort";
            decl += " "+tokens[0].substr(1);
            decl += " () Bool)";
            if(Utils::defineSet.count(tokens[0].substr(1)) == 0){
                variableDeclarations.push_back(decl);
                Utils::defineSet.insert(tokens[0].substr(1));
            }
        }
        else if(tokens[0].compare("%union.pthread_mutexattr_t")==0){
            string decl = "(define-sort";
            decl += " "+tokens[0].substr(1);
            decl += " ()";
            decl += " "+tokens[4];
            decl += ")";
            if(Utils::defineSet.count(tokens[0].substr(1)) == 0){
                variableDeclarations.push_back(decl);
                Utils::defineSet.insert(tokens[0].substr(1));
            }

        }
        else if(tokens[0].compare("%struct.__darwin_pthread_handler_rec")==0){
            continue;
        }
        else if(tokens[0].substr(0,7).compare("%struct")==0 && tokens[0].compare("%struct._opaque_pthread_t")!=0){
            nonMutexStruct.insert(tokens[0]);
            int counter = 0;
            vector<string> defs;
            string name = tokens[0].substr(8);
            for(int i=1;i<tokens.size();i++){
                if(tokens[i].compare("}")==0){
                    break;
                }
                else if(tokens[i].compare("type") == 0 || tokens[i].compare("{") == 0 || tokens[i].compare("=") == 0){
                    continue;
                }
                else{
                    if(tokens[i][0] == '['){
                        string len = tokens[i].substr(1);
                        i += 2;
                        long pos = tokens[i].find("]");
                        string type = tokens[i].substr(0,pos);
                        string finalName = len+type;
                        if(Utils::defineSet.count(finalName) == 0){
                            string def = "(define-sort Array"+finalName+" () (Array (_ BitVec "+Utils::findLog(atoi(len.c_str()))+") "+type+"))";
                            variableDeclarations.push_back(def);
                            Utils::defineSet.insert(finalName);
                        }
                        string fundef = "_"+Utils::myToString(counter)+" () Array"+finalName+")";
                        string lastStoreDef = "_"+Utils::myToString(counter)+" () I32)";
                        defs.push_back(fundef);
                        defs.push_back(lastStoreDef);
                        counter++;
                    }
                    else{
                        long pos = tokens[i].find(",");
                        string type;
                        if(pos != string::npos){
                            type = tokens[i].substr(0,pos);
                        }
                        else{
                            type = tokens[i];
                        }
                        string def = "_"+Utils::myToString(counter)+" () "+type+")";
                        string lastStoreDef = "_"+Utils::myToString(counter)+" () "+type+")";
                        defs.push_back(def);
                        defs.push_back(lastStoreDef);
                        counter++;
                        vector<string> v;
                    }
                }
            }
            
            structDefinitions[tokens[0]] = defs;
        }
        else if(tokens[2].compare("global")==0&&tokens[3][0] != '['){
            string decl = "(declare-fun "+tokens[0].substr(1);
            decl += " () "+tokens[3]+")";
            variableDeclarations.push_back(decl);
            Utils::globalTypeMap.insert(make_pair(tokens[0].substr(1), tokens[3]));
            storeInstructions.push_back(gs.globalStorePart(tokens[0].substr(1),tokens[4].substr(0,tokens[4].length()-1)));
            if(strcmp(tokens[3].c_str(),"%union.pthread_mutex_t")==0 || tokens[3].compare("%struct._opaque_pthread_mutex_t")==0){
                Utils::mutexSet.insert(tokens[0].substr(1));
            }
            else{
                vector<string> v;
                Utils::globalMap.insert(make_pair(tokens[0].substr(1),v));
                Utils::globalStoreCount.insert(make_pair(tokens[0].substr(1),0));
            }
        }
        else if(tokens[3].compare("global")==0 && nonMutexStruct.count(tokens[4])>0){
            string currentName = tokens[0].substr(1);
            vector<string> defs = structDefinitions[tokens[4]];
            for(int i=0;i<defs.size();i++){
                if(i&1){
                    continue;
                }
                string def = "(declare-fun ";
                def += currentName+defs[i];
                variableDeclarations.push_back(def);
                vector<string> defTokens = Utils::split(def);
                if(defTokens[3].substr(0,5).compare("Array") != 0){
                    vector<string> v;
                    string name = defTokens[1];
                    string type = defTokens[3].substr(0,defTokens[3].length()-1);
                    Utils::globalMap[name] = v;
                    Utils::globalTypeMap[name] = type;
                }
                else{
                    string temp = Utils::split(def)[3];
                    temp = temp.substr(5);
                    long pos = temp.find("i");
                    string type1 = temp.substr(0,pos);
                    string type2 = temp.substr(pos+1,temp.length()-(pos+2));
                    string arrayTarget = Utils::split(currentName+defs[i])[0];
                    Utils::arraySizeMap[arrayTarget] = make_pair(type1, type2);
                }
            }
        }
        else if(tokens[3].compare("global")==0&&tokens[4][0] != '['){
            bool isPrimitive = true;
            string decl = "(declare-fun "+tokens[0].substr(1);
            if(tokens[4][0] == '%'){
                isPrimitive = false;
                tokens[4] = tokens[4].substr(1);
            }
            if(tokens[4][tokens[4].length()-1] == '*'){
                tokens[4] = tokens[4].substr(0,tokens[4].length()-1);
            }
            decl += " () "+tokens[4]+")";
            variableDeclarations.push_back(decl);
            Utils::globalTypeMap.insert(make_pair(tokens[0].substr(1),tokens[4]));
            if(isPrimitive){
                if(tokens[5].compare("null,")!=0){
                    storeInstructions.push_back(gs.globalStorePart(tokens[0].substr(1), tokens[5].substr(0,tokens[5].length()-1)));
                }
                else{
                    storeInstructions.push_back(gs.globalStorePart(tokens[0].substr(1), "0"));
                }
            }
            if(strcmp(tokens[4].c_str(),"union.pthread_mutex_t")==0 || tokens[4].compare("struct._opaque_pthread_mutex_t")==0){
                Utils::mutexSet.insert(tokens[0].substr(1));
            }
            else if(tokens[4].compare("struct._opaque_pthread_cond_t")==0){
                Utils::condVarSet.insert(tokens[0].substr(1));
            }
            else{
                vector<string> v;
                Utils::globalMap.insert(make_pair(tokens[0].substr(1),v));
                Utils::globalStoreCount.insert(make_pair(tokens[0].substr(1),0));
            }
        }
        else if(tokens[3].compare("global")==0&&tokens[4][0] == '['){
            string decl1 = "(define-sort Array";
            string tempName = tokens[4].substr(1)+tokens[6].substr(0,tokens[6].length()-1);
            decl1 += tempName;
            decl1 += " () (Array (_ BitVec "+Utils::findLog(atoi((tokens[4].substr(1)).c_str()));
            decl1 += ") "+tokens[6].substr(0,tokens[6].length()-1)+"))";
            if(Utils::defineSet.count(tempName) == 0){
                variableDeclarations.push_back(decl1);
                Utils::defineSet.insert(tempName);
            }
            string decl2 = "(declare-fun ";
            string varName = tokens[0].substr(1);
            decl2 += varName + " () Array"+tempName+")";
            variableDeclarations.push_back(decl2);
            string decl3 = "(declare-fun ";
            decl3 += "l"+varName;
            decl3 += " () I32)";
            variableDeclarations.push_back(decl3);
        }
        else if(tokens[0][0]=='@'){
            string decl1 = "(define-sort Array";
            string tempName = tokens[5].substr(1)+tokens[7].substr(0,tokens[7].length()-1);
            decl1 += tempName;
            decl1 += " () (Array (_ BitVec "+Utils::findLog(atoi((tokens[5].substr(1)).c_str()));
            string bvsize = Utils::findLog(atoi((tokens[5].substr(1)).c_str()));
            decl1 += ") "+tokens[7].substr(0,tokens[7].length()-1)+"))";
            if(Utils::defineSet.count(tempName) == 0){
                variableDeclarations.push_back(decl1);
                Utils::defineSet.insert(tempName);
            }
            string decl2 = "(declare-fun ";
            string varName = tokens[0].substr(1);
            decl2 += varName + " () Array"+tempName+")";
            variableDeclarations.push_back(decl2);
            string decl3 = "(declare-fun ";
            decl3 += "l"+varName;
            decl3 += " () I32)";
            variableDeclarations.push_back(decl3);
            string targetStr = tokens[8];
            targetStr = targetStr.substr(2,targetStr.length()-7);
            for(int i=0;i<targetStr.length();i++){
                string instruction = "(= "+varName+" (store "+varName;
                instruction += " (_ bv"+Utils::myToString(i)+" "+bvsize+")";
                instruction += " (_ bv"+Utils::myToString((int)targetStr[i])+" 8)))";
                storeInstructions.push_back(instruction);
            }
        }
    }
    
    for(int i=0;i<storeInstructions.size();i++){
        if(i!=storeInstructions.size()-1){
            result += " (and";
            result += " "+storeInstructions[i];
            paranthesisCount++;
        }
        else{
            result += " "+storeInstructions[i];
            for(int j=0;j<paranthesisCount;j++){
                result += ")";
            }
            break;
        }
    }
    //cout<<result;
    return result;
}

/*
 * Generates initial declarations of global variables in SMT-LIB.
 */
void putGlobalStoreTypes(){
    for(map<string, int>::iterator itr = Utils::globalStoreCount.begin();itr != Utils::globalStoreCount.end();++itr){
        for(int i=0;i<itr->second;i++){
            Utils::variableTypeMap.insert(make_pair(itr->first+Utils::myToString(i), Utils::globalTypeMap[itr->first]));
        }
    }
}

/*
 * Generates allowed pc map for each bound using breadth first search on instruction map.
 */
void generateAllowedPcMap(){
    
    set<int> usedSet;
    map<string, string> temp = Utils::threadMap;
    temp.insert(Utils::functionPcMap.begin(), Utils::functionPcMap.end());
    for(map<string, string>::iterator itr = temp.begin(); itr != temp.end(); ++itr){
        string currentThread = itr->first;
        queue<pair<string, vector<int> > > parentQueue;
        queue<pair<string, vector<int> > > childQueue;
        parentQueue.push(threadInstructionMap[currentThread][0]);
        vector<string> initialPc;
        initialPc.push_back(temp[currentThread]);
        threadAllowedPcsMap[currentThread][0] = initialPc;
        int instructionIndex = 1;
        int lastPc = atoi(temp[currentThread].data());
        while(!parentQueue.empty()){
            vector<string> nextPcsForMap;
            while(!parentQueue.empty()){
                vector<int> nextPcs = parentQueue.front().second;
                parentQueue.pop();
                for(int i=0; i < nextPcs.size(); ++i){
                    if(usedSet.count(nextPcs[i])>0 || (currentThread.compare("main") == 0 && mainLastException.length() > 0 && nextPcs[i] >= atoi(mainLastException.c_str()))){
                        continue;
                    }
                    nextPcsForMap.push_back(Utils::myToString(nextPcs[i]));
                    childQueue.push(threadInstructionMap[currentThread][nextPcs[i]-atoi(temp[currentThread].data())]);
                    usedSet.insert(nextPcs[i]);
                }
                
            }
            threadAllowedPcsMap[currentThread][instructionIndex] = nextPcsForMap;
            instructionIndex++;
            if(childQueue.empty()){
                break;
            }
            while(!childQueue.empty()){
                parentQueue.push(childQueue.front());
                childQueue.pop();
            }
            
        }
    }
}