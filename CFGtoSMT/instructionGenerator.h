//
//  instructionGenerator.h
//  CFGtoSMT
//
//  Created by Alican Goksel on 1/22/14.
//  Copyright (c) 2014 Alican Goksel. All rights reserved.
//

#ifndef CFGtoSMT_instructionGenerator_h
#define CFGtoSMT_instructionGenerator_h

#include <string>
#include <vector>
#include <map>

using namespace std;

class instructionGenerator{
public:
    string convert(vector<string>&);
    void setCurrentThread(string&);
    string getCurrentThread();
    void setCurrentStep(int value);
    int getCurrentStep();
    void setStepBound(int value);
    int getStepBound();
    void setMutexPresent(bool value);
    bool getIsMutexPresent();

private:
    string storeType(string&, string&, string&, bool, vector<string>&);
    string loadType(string&, string&, string&, bool);
    string branchConditionalType(string&, string&, string&);
    string branchUnconditionalType(string&);
    string mutexLockType(string&);
    string mutexUnlockType(string&);
    string waitType(string&, string&);
    string signalType(string&);
    string mallocType(string&);
    string objectSizeType(string& target);
    string strCopyType(string& src, string& target, string& size);
    string phiType(string&, string&, string&, string&, string&, string&);
    string addType(string&, string&, string&, string&);
    string mulType(string&, string&, string&);
    string truncType(string&, string&, string&);
    string zextType(string&, string&, string&, string&);
    string andType(string&, string&, string&, string&);
    string orType(string&, string&, string&);
    string compareType(string&, string&, string&, string&, string&);
    string bitcastType(string&, string&, string&, string&, string&);
    string getelementptrTypeArray(string&, string&, string&, string&);
    string getelementptrTypeStruct(vector<string>&);
    string callType(string&, string&, int, vector<string>&);
    string returnType(string&);
    string stepThreadPart(string&, bool);
    string lastStorePart(string&, string&, string&, string&, string&, string&, bool);
    
    string currentThread;
    int currentStep;
    int stepBound;
    bool isMutexPresent;
    bool isLastOperationGetPtr;
    bool isLastOperationGetPtrArray;
    string pointerArrayIndex;
    string pointerArray;
    string lastPointer;
    map<string, string> globalPointerMap;
};

#endif
