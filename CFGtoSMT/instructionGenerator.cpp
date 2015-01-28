//
//  instructionGenerator.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 1/22/14.
//  Copyright (c) 2014 Alican Goksel. All rights reserved.
//

#include "instructionGenerator.h"
#include "Utils.h"
#include <cstdlib>

string instructionGenerator::convert(vector<string>& currentTokens){
    
    string result = "";
    bool isStore = false;
    string currentPc = currentTokens[0];
    bool isCall = false;
    string activeMutex = "";
    string activeCond = "";
    string activeMallocVar = "";
    string activeCopyVar = "";
    bool isLock = false;
    if(currentTokens[2].compare("call")==0){
        isCall = true;
    }
    
    result += stepThreadPart(currentPc, isCall);
    if(currentTokens[2].compare("i1")!=0
       && currentTokens[0].compare(";")!=0
       && currentTokens[0].compare("bb:")!=0
       && currentTokens[0].substr(0,1).compare(".")!=0
       && currentTokens[2].compare("call")!=0
       &&currentTokens[1].compare("unreachable")!=0
       &&currentTokens[1].compare("ret")!=0)
    {
        result += " (and";
    }
    if(currentTokens[3].compare("icmp")==0){
        string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = "Bool";
        Utils::variableTypeMap.insert(make_pair(var, type));
        result += compareType(currentTokens[1], currentTokens[4], currentTokens[6], currentTokens[7], currentTokens[5]);
    }
    //if branching, no need to call pc incrementation part.
    else if(currentTokens[2].compare("i1")==0){
        result += branchConditionalType(currentTokens[3], currentTokens[5], currentTokens[7]);
    }
    else if(currentTokens[2].compare("label")==0){
        result = result.substr(0,result.length()-5);
        result += branchUnconditionalType(currentTokens[3]);
    }
    else if(currentTokens[3].compare("alloca") == 0){
        string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[4].substr(0,currentTokens[4].length()-1);
        long pos = type.find("*");
        if(pos!=string::npos){
            type = type.substr(0,pos);
        }
        Utils::variableTypeMap[var] = type;
    }
    else if(currentTokens[6].compare("@pthread_mutex_lock(%union.pthread_mutex_t*")==0 ||
            currentTokens[6].compare("@pthread_mutex_lock(%struct._opaque_pthread_mutex_t*")==0){
        result += mutexLockType(currentTokens[7]);
        activeMutex = currentTokens[7];
        isLock = true;
    }
    else if(currentTokens[6].compare("@pthread_mutex_unlock(%union.pthread_mutex_t*")==0 ||
            currentTokens[6].compare("@pthread_mutex_unlock(%struct._opaque_pthread_mutex_t*")==0){
        result += mutexUnlockType(currentTokens[7]);
        activeMutex = currentTokens[7];
        isLock = false;
    }
    else if(currentTokens[6].length()>17 && currentTokens[6].substr(6,17).compare("pthread_cond_wait")==0){
        result += waitType(currentTokens[7], currentTokens[9]);
        activeMutex = currentTokens[9].substr(1,currentTokens[9].length()-2);
        activeCond = currentTokens[7].substr(1,currentTokens[7].length()-2);
        isLock = false;
    }
    else if(currentTokens[6].length()>20 && currentTokens[6].substr(0,20).compare("@pthread_cond_signal") == 0){
        result += signalType(currentTokens[7]);
        activeCond = currentTokens[7].substr(1,currentTokens[7].length()-2);
    }
    else if(currentTokens[5].length() > 7 && currentTokens[5].substr(1,6).compare("malloc")==0){
        string globalVar = Utils::mallocPcMap[currentTokens[0]];
        string target = currentTokens[1];
        target = currentThread+Utils::insertTemp(target).substr(1);
        string type = currentTokens[4];
        int lastPos;
        lastPos = type.find('*');
        if(lastPos != string::npos){
            type = type.substr(0,lastPos);
        }
        result += mallocType(globalVar);
        activeMallocVar = globalVar;
        Utils::variableTypeMap.insert(make_pair(target, type));
    }
    else if(currentTokens[5].length() > 16 && currentTokens[5].substr(0,16).compare("@llvm.objectsize") == 0){
        string target = currentTokens[1];
        result += objectSizeType(target);
        Utils::variableTypeMap.insert(make_pair(target, "i64"));
    }
    else if(currentTokens[5].length() > 13 && currentTokens[5].substr(0,13).compare("@__memcpy_chk") == 0){
        string src = currentTokens[13].substr(1,currentTokens[13].length()-2);
        string size = currentTokens[19].substr(0,currentTokens[17].length()-2);
        activeCopyVar = lastPointer;
        result += strCopyType(src, lastPointer, size);
    }
    else if(currentTokens[3].compare("phi")==0){
        string value1 = currentTokens[6].substr(0,currentTokens[6].length()-1);
        string value2 = currentTokens[10].substr(0,currentTokens[10].length()-1);
        result += phiType(currentTokens[1], value1, currentTokens[7],
                          value2, currentTokens[11], currentTokens[4]);
        
        string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[4];
        if(type.compare("i1") == 0){
            type = "Bool";
        }
        Utils::variableTypeMap.insert(make_pair(var,type));
    }
    else if(currentTokens[3].compare("add")==0){
        string val1;
        string val2;
        if(currentTokens[5].substr(0,1).compare("i")==0){
            val1 = currentTokens[6].substr(0,currentTokens[6].length()-1);
            val2 = currentTokens[7];
        }
        else{
            val1 = currentTokens[5].substr(0, currentTokens[5].length()-1);
            val2 = currentTokens[6];
        }
        string var1 = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[4];
        if(type.compare("nsw") == 0){
            type = currentTokens[5];
        }
        Utils::variableTypeMap.insert(make_pair(var1, type));
        result += addType(currentTokens[1], val1, val2, type);
    }
    else if(currentTokens[3].compare("mul")==0){
        string val1;
        string val2;
        if(currentTokens[5].substr(0,1).compare("i")==0){
            val1 = currentTokens[6].substr(0,currentTokens[6].length()-1);
            val2 = currentTokens[7];
        }
        else{
            val1 = currentTokens[5].substr(0, currentTokens[5].length()-1);
            val2 = currentTokens[6];
        }
        string var1 = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        Utils::variableTypeMap.insert(make_pair(var1, "i32"));
        result += mulType(currentTokens[1], val1, val2);
    }
    else if(currentTokens[3].compare("trunc")==0){
        string target = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[7];
        Utils::variableTypeMap[target] = type;
        int srcLen = atoi(currentTokens[4].substr(1).c_str());
        int targetLen = atoi(currentTokens[7].substr(1).c_str());
        string diff = Utils::myToString(srcLen - targetLen - 1);
        result += truncType(target, currentTokens[5], diff);
        
    }
    else if(currentTokens[3].compare("zext") == 0){
        string target = currentThread + Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[7];
        Utils::variableTypeMap[target] = type;
        result += zextType(target, currentTokens[4], currentTokens[5], currentTokens[7]);
    }
    else if(currentTokens[3].compare("and") == 0){
        string target = currentTokens[1];
        string val1 = currentTokens[5].substr(0,currentTokens[5].length()-1);
        string val2 = currentTokens[6];
        
        string temp = currentThread+Utils::insertTemp(target).substr(1);
        string type = currentTokens[4];
        if(type.compare("i1") == 0){
            type = "Bool";
        }
        Utils::variableTypeMap.insert(make_pair(temp, type));
        result += andType(temp, val1, val2, currentTokens[4]);
    }
    else if(currentTokens[3].compare("or") == 0){
        string target = currentTokens[1];
        string val1 = currentTokens[5].substr(0,currentTokens[5].length()-1);
        string val2 = currentTokens[6];
        
        string temp = currentThread+Utils::insertTemp(target).substr(1);
        Utils::variableTypeMap.insert(make_pair(temp, "Bool"));
        result += orType(temp, val1, val2);
    }
    else if(currentTokens[3].compare("bitcast")==0 || currentTokens[3].compare("sext")==0){
        string var1 = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type1 = currentTokens[7];
        if(type1.find("*") != string::npos){
            type1 = type1.substr(0,type1.length()-1);
        }
        Utils::variableTypeMap.insert(make_pair(var1, type1));
        string var2 = currentThread+Utils::insertTemp(currentTokens[5]).substr(1);
        string type2 = currentTokens[4];
        if(type2.find("*") != string::npos){
            type2 = type2.substr(type2.length()-1);
        }
        Utils::variableTypeMap.insert(make_pair(var2, type2));
        result += bitcastType(var1,currentTokens[4],currentTokens[7],var2,currentTokens[3]);
    }
    else if(currentTokens[3].compare("getelementptr")==0){
        if(currentTokens[5][0] == '['){
            string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
            string tempType = currentTokens[7];
            string type = tempType.substr(0,tempType.length()-2);
            Utils::variableTypeMap.insert(make_pair(var, type));
            result += getelementptrTypeArray(var, currentTokens[8], currentTokens[10], currentTokens[12]);
        }
        else{
            string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
            string type = "i32";
            Utils::variableTypeMap[var] = type;
            result += getelementptrTypeStruct(currentTokens);
            isLastOperationGetPtr = true;
        }
    }
    else if(currentTokens[1].compare("store")==0){
        result += storeType(currentTokens[3], currentTokens[5], currentTokens[7], isLastOperationGetPtr, currentTokens);
        isLastOperationGetPtr = false;
        if(currentTokens[5][0] == '@'){
            isStore = true;
        }
        
    }
    else if(currentTokens[3].compare("load")==0 && currentTokens[4].compare("%struct._opaque_pthread_t**") !=0){
        string var = currentThread+Utils::insertTemp(currentTokens[1]).substr(1);
        string type = currentTokens[4];
        if(type[type.length()-1] == '*' && type[type.length()-2] == '*'){
            lastPointer = currentTokens[5].substr(1,currentTokens[5].length()-2);
            globalPointerMap.insert(make_pair(var, lastPointer));
        }
        size_t pos = type.find("*");
        if(pos!=string::npos){
            type = type.substr(0,pos);
        }
        Utils::variableTypeMap.insert(make_pair(var, type));
        result += loadType(var,currentTokens[5], currentTokens[7], isLastOperationGetPtr);
        isLastOperationGetPtr = false;
    }
    else if(currentTokens[3].compare("call") == 0 && currentTokens[4].compare("fastcc") != 0){
        int funcIndex = -1;
        if(currentTokens[4][0] == '@'){
            funcIndex = 4;
        }
        else{
            funcIndex = 5;
        }
        long pos = currentTokens[funcIndex].find("(");
        string func = currentTokens[funcIndex].substr(1,pos-1);
        string target = Utils::insertTemp(currentTokens[1]).substr(1);
        if(Utils::functionPcMap.count(func) > 0){
            result += callType(target, func, funcIndex, currentTokens);
        }
        string type = currentTokens[4];
        Utils::variableTypeMap[currentThread+target] = type;
    }
    
    string storeVariable = "";
    string pcNow = "-1";
    //If store instruction, set pcNow and modify the last store instructions.
    if(isStore){
        storeVariable = currentTokens[5].substr(1,currentTokens[5].length()-1);
        pcNow = currentTokens[0];
    }
    
    if(currentTokens[2].compare("call")!=0){
        result += lastStorePart(storeVariable, pcNow, activeMutex, activeCond, activeMallocVar, activeCopyVar, isLock);
    }
    
    if (currentTokens[1].compare("unreachable") == 0 || currentTokens[1].compare("ret")==0)
    {
        if(Utils::functionPcMap.count(currentThread)>0 && currentTokens[3].compare("null") != 0){
            if(Utils::returnMap.count(currentThread) > 0 && currentTokens[3].compare("undef")!=0){
                result += " (and";
            }
            result += " (and (= call_"+currentThread+Utils::myToString(currentStep+1)+" false)";
            if(Utils::returnMap.count(currentThread)>0 && currentTokens[3].compare("undef")!=0){
                result += " (= "+Utils::returnMap[currentThread];
                string target = currentTokens[3];
                if(target[0] == '%'){
                    result += " "+currentThread+Utils::insertTemp(target).substr(1)+"))";
                }
                else{
                    result += " (_ bv"+target+" "+currentTokens[2].substr(1)+")))";
                }
            }
            result += " false))";
        }
        else{
            Utils::threadLastPcMap[currentThread] = atoi(currentTokens[0].c_str())-1;
            result += " false)";
        }
    }
    else{
        result += ")";
    }
    
    return result;
}

/*
 * Checking the thread and pc of that thread.
 */
string instructionGenerator::stepThreadPart(string& pc, bool isCall){
    
    string result = " (and (and";
    //    for(int i=0;i<Utils::threadMap.size();i++){
    //        result += " (and";
    //    }
    result += " "+currentThread+Utils::myToString(currentStep);
    if(!isCall){
        result += " (and";
    }
    result += " (=";
    result += " "+currentThread + "pc" + Utils::myToString(currentStep);
    result += " (_ bv" + pc;
    result += " 32))";
    return result;
}

/*
 * Conversion of compare type instruction.
 */
string instructionGenerator::compareType(string& resultParam, string& type, string& param1, string& param2, string& resultType){
    resultParam = Utils::insertTemp(resultParam).substr(1);
    string result = " (= ";
    Utils::variableTypeMap.insert(make_pair(currentThread+resultParam, "Bool"));
    result += currentThread+resultParam;
    result += " (";
    if(type.compare("sgt")==0 || type.compare("ugt")==0){
        result += "bvsgt";
    }
    else if(type.compare("slt")==0 || type.compare("ult")==0){
        result += "bvslt";
    }
    else if(type.compare("eq")==0){
        //Bu bveq fln da olabilir bakmak lazim.
        result += "=";
    }
    if(param2.compare("null")==0){
        result += " init"+lastPointer+Utils::myToString(currentStep)+" true";
    }
    else{
        resultType = resultType.substr(1);
        if(param1[0] == '%'){
            string tempParam1 = param1;
            tempParam1 = Utils::insertTemp(tempParam1);
            size_t pos = tempParam1.find(",");
            result += " "+currentThread+tempParam1.substr(1,pos-1);
        }
        else{
            result += " (_ bv"+param1+" "+resultType+")";
        }
        
        if(param2[0] == '%'){
            size_t pos = param2.find(",");
            if(pos != string::npos){
                result += " "+currentThread+Utils::insertTemp(param2.substr(1,pos-2));
            }
            else{
                result += " "+currentThread+Utils::insertTemp(param2.substr(1));
            }
        }
        else{
            if(param2[0] == '-'){
                result += " (bvneg (_ bv"+param2.substr(1)+" "+resultType+"))";
            }
            else{
                result += " (_ bv"+param2+" "+resultType+")";
            }
        }
    }
    
    result += "))";
    
    //cout<<result<<endl;
    return result;
}

/*
 * Conversion of conditional branch type instruction.
 */
string instructionGenerator::branchConditionalType(string& condVariable, string& label1, string& label2){
    //string s = label1.substr(0,label1.length()-1);
    size_t pos1 = label1.find(",");
    size_t pos2 = label2.find(",");
    if(pos1 == string::npos){
        pos1 = label1.length();
    }
    if(pos2 == string::npos){
        pos2 = label2.length();
    }
    string block1pc = Utils::blockMap[currentThread+"b"+label1.substr(1,pos1-1)];
    string block2pc = Utils::blockMap[currentThread+"b"+label2.substr(1,pos2-1)];
    condVariable = Utils::insertTemp(condVariable);
    string result = " (or";
    if(condVariable.compare("true,") != 0 && condVariable.compare("false,") != 0){
        result += " (and "+currentThread+condVariable.substr(1,condVariable.length()-2);
    }
    else{
        result += " (and "+condVariable.substr(0,condVariable.length()-1);
    }
    result += " (= "+currentThread+"pc"+Utils::myToString(currentStep+1);
    result += " (_ bv"+block1pc+" 32)))";
    if(condVariable.compare("true,") != 0 && condVariable.compare("false,") != 0){
        result += " (and (not "+currentThread+condVariable.substr(1,condVariable.length()-2)+")";
    }
    else{
        if(condVariable.compare("true,") == 0){
            result += " (and false";
        }
        else{
            result += " (and true";
        }
    }
    result += " (= "+currentThread+"pc"+Utils::myToString(currentStep+1);
    result += " (_ bv"+block2pc+" 32))))";
    
    //cout<<result<<endl;
    return result;
}

/*
 * Conversion of mutex lock type instruction
 */
string instructionGenerator::mutexLockType(string& mutex){
    string result = "";
    mutex = mutex.substr(1,mutex.length()-2);
    result += " (= "+mutex+Utils::myToString(currentStep)+" false)";
    return result;
}

/*
 * Conversion of mutex unlock type instruction
 */
string instructionGenerator::mutexUnlockType(string& mutex){
    string result = "";
    mutex = mutex.substr(1,mutex.length()-2);
    result += " "+mutex+Utils::myToString(currentStep);
    return result;
}

/*
 * Conversion of condition variable wait type instruction
 */
string instructionGenerator::waitType(string& condVar, string& mutex){
    string realCondVar = condVar.substr(1,condVar.length()-2);
    string realMutex = mutex.substr(1,mutex.length()-2);
    string result = " (and "+realMutex+Utils::myToString(currentStep);
    result += " (= "+realCondVar+Utils::myToString(currentStep+1);
    result += " true))";
    return result;
}

/*
 * Conversion of condition variable signal type instruction
 */
string instructionGenerator::signalType(string& condVar){
    string realCondVar = condVar.substr(1,condVar.length()-2);
    string result = " (= "+realCondVar+Utils::myToString(currentStep+1);
    result += " false)";
    return result;
}

/*
 * Conversion of malloc type instruction. Taking the global variable which is the target of the operation
 * and making its init_var values true or false for the next steps.
 */
string instructionGenerator::mallocType(string& globalVar){
    
    //string result = " (or (= init"+globalVar+Utils::myToString(currentStep+1)+" true)";
    //result += " (= init"+globalVar+Utils::myToString(currentStep+1)+" false))";
    string result = " (not init"+globalVar+Utils::myToString(currentStep+1)+")";
    return result;
}

/*
 * Conversion of object size type instruction. This is used in LLVM to check if malloc successfully allocated place from memory.
 * However, we are checking it with init_var variable so, the target is given 1 default value to pass the test.
 * It might change in the future for better conversion.
 */
string instructionGenerator::objectSizeType(string &target){
    
    target = currentThread+Utils::insertTemp(target).substr(1);
    string result = "(= "+target+" (_ bv1 64))";
    return result;
}

/*
 * Conversion of strcpy type instruction. The src is the source string global and the target is the given global variable.
 * This function copies all the characters inside of the src variable to the target_var variable of the given target.
 */
string instructionGenerator::strCopyType(string &src, string &target, string& size){
    int limit = atoi(size.c_str());
    string bvsize = Utils::findLog(limit);
    string result = "";
    //NOT SURE IF THIS CODE IS WORKING CORRECTLY SO CURRENTLY IT IS COMMENTED OUT.
//    for(int i=0;i<limit;i++){
//        if(i!=limit-1){
//            
//            result += " (and";
//        }
//        result += " (= target"+target+Utils::myToString(currentStep+1)+" (store target"+target+Utils::myToString(currentStep)+" (_ bv"+Utils::myToString(i)+" "+bvsize+") (select "+src+" (_ bv"+Utils::myToString(i)+" "+bvsize+"))))";
//    }
//    for(int i=0;i<limit-1;i++){
//        result += ")";
//    }
    
    if(Utils::targetSizeMap.count("target"+target) == 0){
        Utils::targetSizeMap["target"+target] = bvsize;
    }
    
    return result;
}

/*
 * Conversion of phi type instruction
 */
string instructionGenerator::phiType(string & target, string & value1, string & label1, string & value2, string & label2, string& type){
    
    int labelVal1, labelVal2;
    if(label1.compare("%0")==0){
        labelVal1 = 0;
    }
    else{
        labelVal1 = atoi((Utils::blockMap[currentThread+"b"+label1.substr(1)]).c_str());
    }
    
    if(label2.compare("%0")==0){
        labelVal2 = 0;
    }
    else{
        labelVal2 = atoi((Utils::blockMap[currentThread+"b"+label2.substr(1)]).c_str());
    }
    
    int maximum = max(labelVal1, labelVal2);
    
    string result = " (or";
    result += " (and (bvslt "+currentThread+"pc"+Utils::myToString(currentStep-1)+" (_ bv"+Utils::myToString(maximum)+" 32))";
    result += " (= "+currentThread+Utils::insertTemp(target).substr(1);
    if(maximum == labelVal1){
        if(value2[0] == '%'){
            result += " "+currentThread+Utils::insertTemp(value2).substr(1);
        }
        else{
            if(value2.compare("true") == 0 || value2.compare("false") == 0){
                result += " "+value2;
            }
            else{
                if(value2[0] != '-'){
                    result += " (_ bv"+value2+" "+type.substr(1)+")";
                }
                else{
                    result += " (bvneg (_ bv"+value2.substr(1)+" "+type.substr(1)+"))";
                }
            }
        }
    }
    else{
        if(value1[0] == '%'){
            result += " "+currentThread+Utils::insertTemp(value1).substr(1);
        }
        else{
            if(value1.compare("true") == 0 || value1.compare("false") == 0){
                result += " "+value1;
            }
            else{
                if(value1[0] != '-'){
                    result += " (_ bv"+value1+" "+type.substr(1)+")";
                }
                else{
                    result += " (bvneg (_ bv"+value1.substr(1)+" "+type.substr(1)+"))";
                }
            }
            
        }
    }
    
    result += "))";
    
    result += " (and (not (bvslt "+currentThread+"pc"+Utils::myToString(currentStep-1)+" (_ bv"+Utils::myToString(maximum)+" 32)))";
    result += " (= "+currentThread+Utils::insertTemp(target).substr(1);
    if(maximum == labelVal1){
        if(value1[0] == '%'){
            result += " "+currentThread+Utils::insertTemp(value1).substr(1);
        }
        else{
            if(value1.compare("true") == 0 || value1.compare("false") == 0){
                result += " "+value1;
            }
            else{
                result += " (_ bv"+value1+" 32)";
            }
            
        }
    }
    else{
        if(value2[0] == '%'){
            result += " "+currentThread+Utils::insertTemp(value2).substr(1);
        }
        else{
            if(value2.compare("true") == 0 || value2.compare("false") == 0){
                result += " "+value2;
            }
            else{
                result += " (_ bv"+value2+" 32)";
            }
            
        }
    }
    
    result += ")))";
    
    return result;
}

/*
 * Conversion of add type instruction
 */
string instructionGenerator::addType(string& target, string& val1, string& val2, string& type){
    string result = " (= "+currentThread+Utils::insertTemp(target).substr(1);
    result += " (bvadd";
    if (val1.substr(0,1).compare("%")==0) {
        val1 = currentThread+Utils::insertTemp(val1).substr(1);
        result += " "+val1;
    }
    else{
        result += " (_ bv"+val1+" "+type.substr(1)+")";
    }
    
    if (val2.substr(0,1).compare("%")==0) {
        val2 = currentThread+Utils::insertTemp(val2).substr(1);
        result += " "+val2;
    }
    else{
        if(val2.substr(0,1).compare("-")==0){
            result += " (bvneg (_ bv"+val2.substr(1)+" 32))";
        }
        else{
            result += " (_ bv"+val2+" "+type.substr(1)+")";
        }
    }
    
    result += "))";
    
    return result;
}

/*
 * Conversion of mul type instruction
 */
string instructionGenerator::mulType(string& target, string& val1, string& val2){
    string result = " (= "+currentThread+Utils::insertTemp(target).substr(1);
    result += " (bvmul";
    if (val1.substr(0,1).compare("%")==0) {
        val1 = currentThread+Utils::insertTemp(val1).substr(1);
        result += " "+val1;
    }
    else{
        result += " (_ bv"+val1+" 32)";
    }
    
    if (val2.substr(0,1).compare("%")==0) {
        val2 = currentThread+Utils::insertTemp(val2).substr(1);
        result += " "+val2;
    }
    else{
        result += " (_ bv"+val2+" 32)";
    }
    
    result += "))";
    
    return result;
}

/*
 * Conversion of trunc type instruciton
 */
string instructionGenerator::truncType(string& target, string& source, string& diff){
    
    string result = " (=";
    result += " "+target;
    result += " ((_ extract "+diff;
    result += " 0)";
    string realSrc = currentThread+Utils::insertTemp(source).substr(1);
    result += " "+realSrc;
    result += "))";
    
    return result;
}

/*
 * Conversion of zero extend type instruction
 * CHECK THIS!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
 */
string instructionGenerator::zextType(string& target, string& srcLen, string& src, string& targetLen){
    
    string realSrc = currentThread+Utils::insertTemp(src).substr(1);
    string result = " (or";
    result += " (and "+realSrc+" (= "+target+" (_ bv1 "+targetLen.substr(1)+")))";
    result += " (and (not "+realSrc+") (= "+target+" (_ bv0 "+targetLen.substr(1)+"))))";
    return result;
}

/*
 * Conversion of and type instruction
 */
string instructionGenerator::andType(string& target, string & val1, string & val2, string& type){
    
    string result = " (= "+target;
    val1 = currentThread+Utils::insertTemp(val1).substr(1);
    if(val2[0] == '%'){
        val2 = currentThread+Utils::insertTemp(val2).substr(1);
    }
    else{
        val2 = "(_ bv1 8)";
    }
    if(type.compare("i1") == 0){
        result += " (and "+val1+" "+val2+"))";
    }
    else{
        result += " (bvand "+val1+" "+val2+"))";
    }
    return result;
}

/*
 * Conversion of or type instruction
 */
string instructionGenerator::orType(string& target, string & val1, string & val2){
    
    string result = " (= "+target;
    val1 = currentThread+Utils::insertTemp(val1).substr(1);
    val2 = currentThread+Utils::insertTemp(val2).substr(1);
    result += " (or "+val1+" "+val2+"))";
    return result;
}

/*
 * Conversion of bitcast type instruction.
 */
string instructionGenerator::bitcastType(string& target, string& fromSize, string& toSize, string& src, string& type){
    
    string result = " (=";
    result += " "+target;
    if(type.compare("bitcast")==0){
        result += " ((_ zero_extend";
    }
    else
    {
        result += " ((_ sign_extend";
    }
    
    result += " "+Utils::myToString(atoi(toSize.substr(1).c_str()) - atoi(fromSize.substr(1).c_str()));
    result += ") "+src+"))";
    //cout<<result;
    return result;
}

/*
 * Conversion of get element pointer type instruction with array parameter.
 * MUHTEMTELEN YENI SEYLER EKLEMEK LAZIM!!!!!!!!!!!!!!!!!!!!!!!!
 */
string instructionGenerator::getelementptrTypeArray(string& target, string& array, string& firstPtr, string& src){
    
    string result = " (=";
    result += " "+target;
    result += " (select";
    result += " "+array.substr(1,array.length()-2);
    //NEDEN 4, 4 olmamasi lazim, array size inin logu olacak.
    result += " ((_ extract 4";
    result += " "+firstPtr.substr(0,firstPtr.length()-1)+")";
    result += " "+currentThread+Utils::insertTemp(src).substr(1)+")))";
    
    //cout<<result<<endl;
    return result;
    
    return "";
}

/*
 * Conversion of get element pointer type instruction with struct parameter.
 */
string instructionGenerator::getelementptrTypeStruct(vector<string> & tokens){
    
    string target = currentThread+Utils::insertTemp(tokens[1]).substr(1);
    string source = tokens[6].substr(1,tokens[6].length()-2);
    if(Utils::functionParameterMap[currentThread][source][0]-'0'>9){
        source = Utils::functionParameterMap[currentThread][source];
    }
    string offset = tokens[10];
    long pos;
    pos = tokens[10].find(",");
    if(pos != string::npos){
        offset = offset.substr(0,pos);
        isLastOperationGetPtrArray = true;
        pointerArrayIndex = currentThread+Utils::insertTemp(tokens[12]).substr(1);
        pointerArray = source+"_"+offset;
    }
    
    Utils::localPointerMap[target] = source+"_"+offset;
    
    return "";
}

/*
 * Conversion of unconditional branch type instruction.
 */
string instructionGenerator::branchUnconditionalType(string& label){
    
    string blockPc = Utils::blockMap[currentThread+"b"+label.substr(1)];
    string result = " (= "+currentThread+"pc"+Utils::myToString(currentStep+1);
    result += " (_ bv"+blockPc+" 32))";
    
    //cout<<result<<endl;
    return result;
}

/*
 * Conversion of store type instruction.
 */
string instructionGenerator::storeType(string& value, string& target, string& align, bool isPointer, vector<string>& tokens){
    
    
    //(= targetx (store targetx (_ bv0 bvsize) (_ bvvalue 8)))
    string result = "";
    if(target.substr(0,3).compare("get") == 0){
        result += " (= "+tokens[10].substr(1,tokens[10].length()-2);
        result += " (store "+tokens[10].substr(1,tokens[10].length()-2)+" (_ bv"+tokens[14].substr(0,1)+" "+Utils::findLog(atoi(tokens[7].substr(2).c_str()))+")";
        string tempValue = "";
        if(value[0]=='%'){
            tempValue = Utils::insertTemp(value);
            tempValue = currentThread+tempValue.substr(1,tempValue.length()-2);
        }
        else{
            tempValue = " (_ bv"+value.substr(0,value.length()-1)+" 32)";
        }

        result += " "+tempValue+")";
    }
    else{
        target = Utils::insertTemp(target.substr(0,target.length()-1));
        if(globalPointerMap.count(currentThread+target) != 0){
            result += " (= target"+globalPointerMap[currentThread]+Utils::myToString(currentStep);
            result += " (store ";
            string newTarget = "target"+globalPointerMap[currentThread+target]+Utils::myToString(currentStep);
            result += " (_ bv0 "+Utils::targetSizeMap["target"+globalPointerMap[currentThread+target]]+") (_ bv"+value.substr(0,value.length()-1)+" 8))";
        }
        else if(isLastOperationGetPtrArray){
            string realTarget = currentThread+target;
            string tempValue = currentThread+value.substr(0,value.length()-1);
            result += " (= "+pointerArray +" (store "+pointerArray;
            result += " ((_ extract "+Utils::myToString(atoi(Utils::findLog(atoi(Utils::arraySizeMap[pointerArray].first.c_str())).c_str())-1);
            result += " 0) "+pointerArrayIndex+")";
            result += " "+tempValue+")";
            isLastOperationGetPtrArray = false;
        }
        else{
            result += " (=";
            if(isPointer){
                string tempTarget = currentThread+Utils::insertTemp(target).substr(1);
                string realTarget = Utils::localPointerMap[tempTarget];
                result += " "+realTarget;
            }
            if(target[0]=='@'){
                result += " "+target.substr(1)+"_"+Utils::myToString(currentStep+1);
            }
            else if(target[0]=='%'){
                result += " "+currentThread+target.substr(1);
            }
            
            if(value[0]=='%'){
                string tempValue = Utils::insertTemp(value);
                result += " "+currentThread+tempValue.substr(1,tempValue.length()-2);
            }
            else{
                result += " (_ bv"+value.substr(0,value.length()-1)+" "+tokens[2].substr(1)+")";
            }
            
        }
    }
    result += ")";
    //cout<<result;
    return result;
}

/*
 * Conversion of load type instruction.
 */
string instructionGenerator::loadType(string& target, string& value, string& align, bool isPointer){
    string result = "";
    if(value[0]=='%'){
        string tempVal = value;
        tempVal = Utils::insertTemp(tempVal);
        tempVal = tempVal.substr(1,tempVal.length()-2);
        result += " (= "+target;
        if(isLastOperationGetPtrArray){
            result += " (select "+pointerArray;
            result += " ((_ extract "+Utils::myToString(atoi(Utils::findLog(atoi(Utils::arraySizeMap[pointerArray].first.c_str())).c_str())-1);
            result += " 0) "+pointerArrayIndex+")))";
            isLastOperationGetPtrArray = false;
        }
        else if(Utils::localPointerMap.count(currentThread+tempVal) > 0){
            result += " "+Utils::localPointerMap[currentThread+tempVal]+"_"+Utils::myToString(currentStep)+")";
        }
        else if(globalPointerMap.count(currentThread+tempVal) != 0){
            string newTarget = "target"+globalPointerMap[currentThread+tempVal]+Utils::myToString(currentStep);
            result += " (select "+newTarget+" (_ bv"+Utils::myToString(atoi(align.c_str())-1)+" "+Utils::targetSizeMap["target"+globalPointerMap[currentThread+tempVal]]+")))";
        }
        else{
            result += " "+currentThread+tempVal+")";
        }
    }
    else{
        string tempVal = value;
        tempVal = tempVal.substr(1,tempVal.length()-2);
        result += " (= "+target;
        result += " "+tempVal+"_"+Utils::myToString(currentStep)+")";
    }
    
    //BU QUEUE ICIN SONRADAN DUZELT
    string src = "q_";
    string replTarget = "queue_";
    Utils::myReplaceAll(result, src, replTarget);
    //cout<<result<<endl;
    return result;
}

/*
 * Conversion of call type instruction. Makes call_<function_name> true for next step and initializes parameters.
 */
string instructionGenerator::callType(string & target, string& func, int startIndex, vector<string>& tokens){
    //BUNA BAKMAK LAZIM/
    string result = "";
    int counter = 0;
    string realParam = tokens[startIndex+1];
    for(int i=startIndex;realParam[realParam.length()-1] != ')';i += 2){
        realParam = tokens[i+1];
        if(tokens[i][tokens[i].length()-1] != '*'){
            result += " (and (= ";
            int index = (i-startIndex)/2;
            map<string, string> paramIndex = Utils::functionParameterMap[func];
            for(map<string, string>::iterator itr = paramIndex.begin();itr!=paramIndex.end();++itr){
                if(atoi(itr->second.c_str()) == index){
                    result += func+itr->first;
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
            result += " "+currentThread+param+")";
            counter++;
        }
    }
    
    result += " (= call_"+func+Utils::myToString(currentStep+1)+" true)";
    
        for(int i=counter;i>0;i--){
            result += ")";
        }
    
    return result;
}

/*
 * Setting the last store pc's of the global variables. If no global store is present, the pc's remain the same.
 */
string instructionGenerator::lastStorePart(string& variable, string& pc, string& activeMutex, string& activeCond, string& activeMallocVar, string& activeCopyVar, bool isLock){
    string result = "";
    for(int i=0;i<Utils::globalMap.size()-1;i++){
        result += " (and";
    }
    
    //SANKI BU YANLIS GIBI, -1 lazim degil mi?
    for(int i=0;i<Utils::mutexSet.size();i++){
        result += " (and";
    }
    
    bool oneminus = false;
    //Ayni limit strcpy ye de lazim gibi. parametre de target olcak.
    int mallocLimit = Utils::mallocMap.size();
    if(activeMallocVar.length() > 0 || activeCopyVar.length() > 0){
        oneminus = true;
    }
    for(int i=0;i<Utils::mallocMap.size();i++){
        if(!oneminus){
            result += " (and";
        }
        oneminus = false;
        result += " (and";
    }
    
    int condLimit = Utils::condVarSet.size();
    if(activeCond.length()>0){
        condLimit--;
    }
    
    for(int i=0;i<condLimit;i++){
        result += " (and";
    }
    
    
    map<string, vector<string> >::iterator itr;
    for(itr = Utils::globalMap.begin();itr!=Utils::globalMap.end();++itr){
        if(pc.compare("-1")!=0 && itr->first.compare(variable)==0){
        }
        else{
            result += " (= "+itr->first+"_"+Utils::myToString(currentStep+1)+" "+itr->first+"_"+Utils::myToString(currentStep)+")";
        }
        if(itr != Utils::globalMap.begin()){
            result += ")";
        }
    }
    if(activeMutex.length()>0){
        if(isLock){
            result += " "+activeMutex+Utils::myToString(currentStep+1)+")";
        }
        else{
            result += " (= "+activeMutex+Utils::myToString(currentStep+1)+" false))";
        }
    }
    for(set<string>::iterator itr = Utils::mutexSet.begin();itr!=Utils::mutexSet.end();++itr){
        string currentMutex = *itr;
        if(currentMutex.compare(activeMutex)!=0){
            result += " (= "+currentMutex+Utils::myToString(currentStep+1)+" "+currentMutex+Utils::myToString(currentStep)+"))";
        }
    }
    for(set<string>::iterator itr = Utils::condVarSet.begin();itr!= Utils::condVarSet.end(); itr++){
        string currentCond = *itr;
        if(currentCond.compare(activeCond)!=0){
            result += " (= "+currentCond+Utils::myToString(currentStep+1)+" "+currentCond+Utils::myToString(currentStep)+"))";
        }
    }
    for(map<string, pair<string, string> >::iterator itr = Utils::mallocMap.begin(); itr!= Utils::mallocMap.end(); ++itr){
        string currentVar = itr->first;
        if(currentVar.compare(activeMallocVar) != 0){
            string initVar = " init"+currentVar;
            result += " (="+initVar+Utils::myToString(currentStep+1)+" "+initVar+Utils::myToString(currentStep)+"))";
            
        }
        if(currentVar.compare(activeCopyVar) != 0){
            string targetVar = " target"+currentVar;
            result += " (="+targetVar+Utils::myToString(currentStep+1)+" "+targetVar+Utils::myToString(currentStep)+"))";
        }
    }
    
    result += "))";
    
    //cout<<result<<endl;
    return result;
}

void instructionGenerator::setCurrentStep(int value){
    this->currentStep = value;
}

void instructionGenerator::setCurrentThread(string& value){
    this->currentThread = value;
}