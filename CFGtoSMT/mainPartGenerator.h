//
//  mainPartGenerator.h
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/3/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#ifndef __CFGtoSMT__mainPartGenerator__
#define __CFGtoSMT__mainPartGenerator__

#include <iostream>
#include <string>
#include <map>

using namespace std;

class mainPartGenerator{
    
    int pcCounter;
    map<string, int> globalCounter;
    
public:
    mainPartGenerator();
    string storeType(string&, string&);
    pair<string, string> globalStoreModifier(string&, string&);
    string callType(string&, string&, bool);
    string bitcastType(string&, string&, string&, string&);
    string pcType(string&);
};

#endif /* defined(__CFGtoSMT__mainPartGenerator__) */
