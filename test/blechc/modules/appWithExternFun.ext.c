#include <stdio.h>

#include "blech.h"

#include "appWithExternFun.ext.h"

static int x = 0;
blc_int32 increase_global_state (void){
    return ++x;
}