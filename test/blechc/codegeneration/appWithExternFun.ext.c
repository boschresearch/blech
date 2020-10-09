#include <stdio.h>

#include "blech.h"

#include "appWithExternFun.h"

static int x = 0;
blc_int32 blc_blech_appWithExternFun_myExternFun (void){
    return ++x;
}