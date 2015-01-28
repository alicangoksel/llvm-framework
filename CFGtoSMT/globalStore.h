//
//  globalStore.h
//  CFGtoSMT
//
//  Created by Alican Goksel on 12/9/13.
//  Copyright (c) 2013 Alican Goksel. All rights reserved.
//

#ifndef CFGtoSMT_globalStore_h
#define CFGtoSMT_globalStore_h

#include <string>

using namespace std;

class globalStoreGenerator{
public:
    string globalStorePart(string globalName, string value);
};

#endif
