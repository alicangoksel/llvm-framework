//
//  declarationGenerator.h
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/20/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#ifndef CFGtoSMT_declarationGenerator_h
#define CFGtoSMT_declarationGenerator_h

#include <map>
#include <vector>
#include <set>
#include <string>
using namespace std;

class declarationGenerator{
public:
    vector<string> execute(map<string, vector<string> >&, map<string, string>&, set<string>&, set<string>&, map<string,pair<string, string> >&, int bound);
    vector<string> execute(map<string, string>&);
    vector<string> initialize();
private:
    vector<string> generateGlobalDeclarations(map<string, vector<string> >&, map<string, string>&, set<string>&, set<string>&, map<string, pair<string, string> >&, int bound);
    vector<string> generateLocalDeclarations(map<string, string>&);
    vector<string> globalPart(map<string, vector<string> >&, int bound);
    vector<string> threadPart(map<string, string>&, int bound);
    vector<string> mutexPart(set<string>&, int bound);
    vector<string> condPart(set<string>&, int bound);
    vector<string> mallocPart(map<string, pair<string, string> >&, int bound);
};


#endif
