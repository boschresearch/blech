#include <stdio.h>

#include "blech.h"

#include "blech/appWithExternFun.h"

static int x = 0;
blc_int32 blc_appWithExternFun_myExternFun (void){
    return ++x;
}