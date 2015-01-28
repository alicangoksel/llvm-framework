//
//  globalStore.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/9/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#include "globalStore.h"
#include "Utils.h"

string globalStoreGenerator::globalStorePart(string globalName, string globalValue){
    string result = " (=";
    result += " "+globalName;
    result += " (_ bv"+globalValue+" "+Utils::globalTypeMap[globalName].substr(1)+"))";
    return result;
}