//
//  Utils.h
//  CFGtoSMT
//
//  Created by Alican Goksel on 1/22/14.
//  Copyright (c) 2014 Alican Goksel. All rights reserved.
//

#ifndef CFGtoSMT_Utils_h
#define CFGtoSMT_Utils_h

#include <string>
#include <vector>
#include <map>
#include <set>

using namespace std;

class Utils{
public:
    static string findLog(int value);
    static void replaceiWithI(string& val);
    static void myReplaceAll(string& str, string& from, string& to);
    static string myToString(int i);
    static vector<string> split(string val);
    static string insertTemp(string var);
    static bool isReplaceable(string var);

    static map<string, string> variableTypeMap;
    static map<string, string> globalTypeMap;
    static map<string, vector<string> > globalMap;
    static set<string> mutexSet;
    static set<string> condVarSet;
    static map<string, string> threadMap;
    static map<string, string> functionPcMap;
    static map<string, set<string> > threadFunctionMap;
    static map<string, string> blockMap;
    static map<string, int> globalStoreCount;
    static map<string, string> initialValueMap;
    static map<string, string> condVariableThreadMap;
    static map<string, pair<string, string> > mallocMap;
    static map<string, string> mallocPcMap;
    static map<string, string> targetSizeMap;
    static map<string, map<string, string> > functionParameterMap;
    static map<string, string> returnMap;
    static set<string> defineSet;
    static map<string, int> threadLastPcMap;
    static map<string, string> localPointerMap;
    static map<string, pair<string, string> > arraySizeMap;
};


#endif
