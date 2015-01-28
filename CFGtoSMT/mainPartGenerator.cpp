//
//  mainPartGenerator.cpp
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/3/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#include "mainPartGenerator.h"
#include "Utils.h"
#include <sstream>

mainPartGenerator::mainPartGenerator(){
    
    pcCounter = 0;
}

string mainPartGenerator::pcType(string& pcValue){
    string result = " (=";
    result += " pc"+Utils::myToString(pcCounter);
    result += " (_ bv"+pcValue+" 32))";
    pcCounter++;
    return result;
}

string mainPartGenerator::storeType(string& source, string& target){
    string result = " (=";
    target = target.substr(0,target.length()-1);
    source = source.substr(0,source.length()-1);
    source = Utils::insertTemp(source);
    target = Utils::insertTemp(target);
    
    //Tum globallerin store count unu tutmak lazim. x0, x1 vs de olabililr.
    if(target[0]=='@'){
        if (globalCounter.count(target.substr(1))) {
            globalCounter[target.substr(1)] = 0;
        }
        result += " "+target.substr(1);
        //globalCounter[target.substr(1)]++;
    }
    else if(target[0]=='%'){
        result += " main"+target.substr(1);
    }
    
    if(source[0]=='%'){
        result += " main"+source.substr(1,source.length()-1);
    }
    else{
        result += " (_ bv"+source+" 32)";
    }
    result += ")";
    
    //cout<<result;
    return result;

}

string mainPartGenerator::callType(string& thread, string& parameter, bool isGlobal){
    parameter = Utils::insertTemp(parameter);
    parameter = parameter.substr(1);
    string result = " (=";
    result += " "+thread+"arg";
    if(!isGlobal){
        result += " main";
    }
    else{
        result += " ";
    }
    result += parameter+")";
    return result;
}

string mainPartGenerator::bitcastType(string& target, string& len1, string& source, string& len2){
    string result = " (=";
    
    source = Utils::insertTemp(source);
    target = Utils::insertTemp(target);
    target = target.substr(1);
    source = source.substr(1);
    result += " main"+target;
    
    int length1 = atoi(len1.substr(1).c_str());
    int length2 = atoi(len2.substr(1).c_str());
    if(length1 > length2){
        result += " ((_ extract";
        length2--;
        result += " "+Utils::myToString(length2)+" 0)";
    }
    else{
        result += " ((_ zero_extend";
        result += " "+Utils::myToString(length2 - length1)+=")";
    }
    
    result += " main"+source+="))";
    return result;
}

pair<string, string> mainPartGenerator::globalStoreModifier(string& globalName, string& pcValue){
    string result = " (=";
    result += " l"+globalName+Utils::myToString(pcCounter-1);
    result += " (_ bv"+pcValue+=" 32))";
    string term = "l"+globalName+Utils::myToString(pcCounter-1);
    return make_pair(result, term);
}
    
