//
//  declarationGenerator.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/20/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#include "declarationGenerator.h"
#include "Utils.h"
#include <sstream>
#include <iostream>

vector<string> declarationGenerator::execute(map<string, vector<string> >& globalMap, map<string, string>& threadMap, set<string>& mutexSet, set<string>& condSet,
                                             map<string, pair<string, string> >& mallocMap, int bound){
    
    return generateGlobalDeclarations(globalMap, threadMap, mutexSet, condSet, mallocMap, bound);
}

vector<string> declarationGenerator::execute(map<string, string> & variableTypeMap){
    return generateLocalDeclarations(variableTypeMap);
}

vector<string> declarationGenerator::initialize(){
    vector<string> result;
    result.push_back("(set-logic QF_AUFBV)");
    result.push_back("(set-option :produce-models true)");
    result.push_back("(declare-sort Pair 2)");
    result.push_back("(define-sort I8 () (_ BitVec 8))");
    result.push_back("(define-sort I32 () (_ BitVec 32))");
    result.push_back("(define-sort I64 () (_ BitVec 64))");
    return result;
}

vector<string> declarationGenerator::generateGlobalDeclarations(map<string, vector<string> > & globalMap, map<string, string> & threadMap, set<string>& mutexSet, set<string>& condSet, map<string, pair<string, string> >& mallocMap, int bound){
    vector<string> globals = globalPart(globalMap, bound);
    vector<string> threads = threadPart(threadMap, bound);
    vector<string> mutex = mutexPart(mutexSet, bound);
    vector<string> condition = condPart(condSet, bound);
    vector<string> malloc = mallocPart(mallocMap, bound);
    globals.insert(globals.end(), threads.begin(), threads.end());
    globals.insert(globals.end(), mutex.begin(), mutex.end());
    globals.insert(globals.end(), condition.begin(), condition.end());
    globals.insert(globals.end(), malloc.begin(), malloc.end());
    return globals;
}

vector<string> declarationGenerator::generateLocalDeclarations(map<string, string> & variableTypeMap){
    vector<string> result;
    for(map<string,string>::iterator itr=variableTypeMap.begin();itr!=variableTypeMap.end();++itr){
        string line = "(declare-fun "+itr->first+" () "+itr->second+")";
        result.push_back(line);
    }
    
    return result;
}

vector<string> declarationGenerator::globalPart(map<string, vector<string> >& globalMap, int bound){
    
    vector<string> result;
    for(map<string, vector<string> >::iterator itr = globalMap.begin();itr!=globalMap.end();++itr){
        for(int i=0;i<=bound;i++){
            string line = "(declare-fun "+itr->first+"_"+Utils::myToString(i)+" () "+Utils::globalTypeMap[itr->first]+")";
            result.push_back(line);
        }
    }
    return result;
}

vector<string> declarationGenerator::threadPart(map<string, string>& threadMap, int bound){
    
    vector<string> result;
    for(map<string, string>::iterator itr=threadMap.begin();itr!=threadMap.end();++itr){
        for(int i=0;i<=bound;i++){
            string line1 = "(declare-fun "+itr->first+Utils::myToString(i)+" () Bool)";
            string line2 = "(declare-fun "+itr->first+"pc"+Utils::myToString(i)+" () I32)";
            result.push_back(line1);
            result.push_back(line2);
        }
    }
    for(map<string, string>::iterator itr = Utils::functionPcMap.begin(); itr!= Utils::functionPcMap.end(); ++itr){
        for(int i=0;i<=bound;i++){
            string line1 = "(declare-fun "+itr->first+Utils::myToString(i)+" () Bool)";
            string line2 = "(declare-fun "+itr->first+"pc"+Utils::myToString(i)+" () I32)";
            string line3 = "(declare-fun call_"+itr->first+Utils::myToString(i)+" () Bool)";
            result.push_back(line1);
            result.push_back(line2);
            result.push_back(line3);
        }
    }
    return result;
}

vector<string> declarationGenerator::mutexPart(set<string>& mutexSet, int bound){
    vector<string> result;
    for(set<string>::iterator itr = mutexSet.begin();itr!=mutexSet.end();++itr){
        for(int i=0;i<=bound;i++){
            string line = "(declare-fun "+*itr+Utils::myToString(i)+" () Bool)";
            result.push_back(line);
        }
    }
    
    return result;
}

vector<string> declarationGenerator::condPart(set<string>& condSet, int bound){
    vector<string> result;
    for(set<string>::iterator itr = condSet.begin();itr!=condSet.end();++itr){
        for(int i=0;i<=bound;i++){
            string line = "(declare-fun "+*itr+Utils::myToString(i)+" () Bool)";
            result.push_back(line);
        }
    }
    return result;
}

vector<string> declarationGenerator::mallocPart(map<string, pair<string, string> >& mallocMap, int bound){
    vector<string> result;
    //Bunun sanki step basina olmasi lazim, global degil.
    map<string, pair<string, string> >::iterator itr;
    for(itr = Utils::mallocMap.begin(); itr!= Utils::mallocMap.end(); ++itr){
        if(Utils::defineSet.count(itr->second.second+"i8") == 0){
            string arrayDecl = "(define-sort Array"+itr->second.second+"i8 () (Array (_ BitVec "+Utils::findLog(atoi(itr->second.second.c_str()))+") i8))";
            result.push_back(arrayDecl);
            Utils::defineSet.insert(itr->second.second+"i8");
        }
        for(int i=0; i<=bound;i++){
            string initDecl = "(declare-fun init"+itr->first+Utils::myToString(i)+"() Bool)";
            //Simdilik i8 yapiyoruz, malloc llvm de i64 olarak cevrilmis sikinti var.
            string targetDecl = "(declare-fun target"+itr->first+Utils::myToString(i)+" () Array"+itr->second.second+"i8)";
            result.push_back(initDecl);
            result.push_back(targetDecl);
        }
    }
    
    return result;
}
