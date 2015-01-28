//
//  Utils.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 1/22/14.
//  Copyright (c) 2014 Alican Goksel. All rights reserved.
//

#include "Utils.h"
#include <sstream>

/**
 * Finds the log of given value in base 2.
 */
string Utils::findLog(int value){
    int result = 0;
    while(value != 1){
        result++;
        value = value/2;
    }
    return myToString(result+1);
}

/**
 * Replaces given all occurences of "from" string to "to" string in the given string.
 */
void Utils::myReplaceAll(string &str, string &from, string &to){
    if(from.empty())
        return;
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // In case 'to' contains 'from', like replacing 'x' with 'yx'
    }
}

/**
 * Replaces i with I for types.
 */
void Utils::replaceiWithI(string &val){
    string src1 = "i32";
    string trgt1 = "I32";
    string src2 = "i8";
    string trgt2 = "I8";
    string src3 = "i64";
    string trgt3 = "I64";
    myReplaceAll(val, src1, trgt1);
    myReplaceAll(val, src2, trgt2);
    myReplaceAll(val, src3, trgt3);
}

/**
 * Converts the given integer to string.
 */
string Utils::myToString(int i){
    stringstream ss;
    ss<<i;
    return ss.str();
}

/**
 * Splits the given string using the delimiter " "
 */
vector<string> Utils::split(string line){
    
    vector<string> tokens;
    size_t firstPosition = 0;
    size_t lastPosition = line.find_first_of(" ");
    
    while(lastPosition != string::npos){
        string temp = line.substr(firstPosition,lastPosition-firstPosition);
        
        if(temp.length()>0){
            tokens.push_back(temp);
        }
        
        firstPosition = lastPosition+1;
        lastPosition = line.find_first_of(" ",firstPosition);
        if(lastPosition == string::npos){
            tokens.push_back(line.substr(firstPosition));
        }
    }
    
    return tokens;
}

/**
 * Inserts tmp prefix to local variables when they are only numbers.
 */
string Utils::insertTemp(string var){
    
    if (!isReplaceable(var)) {
        return var;
    }
    
    string prefix = "%";
    string remain = var.substr(1);
    return prefix+"tmp"+remain;
}

/**
 * Checks if the var needs to be suffixed by tmp.
 */
bool Utils::isReplaceable(string var){
    
    if(var[0] == '%' && var[1]-'0'>=0 && var[1]-'0'<10){
        return true;
    }
    return false;
}

map<string, string> Utils::variableTypeMap;
map<string, string> Utils::globalTypeMap;
map<string, vector<string> > Utils::globalMap;
set<string> Utils::mutexSet;
set<string> Utils::condVarSet;
map<string, string> Utils::threadMap;
map<string, string> Utils::functionPcMap;
map<string, set<string> > Utils::threadFunctionMap;
map<string, string> Utils::blockMap;
map<string, int> Utils::globalStoreCount;
map<string, string> Utils::initialValueMap;
map<string, string> Utils::condVariableThreadMap;
map<string, pair<string, string> > Utils::mallocMap;
map<string, string> Utils::mallocPcMap;
map<string, string> Utils::targetSizeMap;
map<string, map<string, string> > Utils::functionParameterMap;
map<string, string> Utils::returnMap;
set<string> Utils::defineSet;
map<string, int> Utils::threadLastPcMap;
map<string, string> Utils::localPointerMap;
map<string, pair<string, string> > Utils::arraySizeMap;

