#include <string.h>

#include "blech.h"

#include "returnsStructFromExternFunction.h"

void blc_returnsStructFromExternFunction_rrr (const blc_bool blc_a,
                     struct blc_returnsStructFromExternFunction_S *blc_retvar) {
    struct blc_returnsStructFromExternFunction_S blc_s;
    memset(&(blc_s), 0, sizeof(struct blc_returnsStructFromExternFunction_S));
    blc_s.i = -7;
    blc_s.j = 3.420000;
    blc_s.a[0].x = 1;
    blc_s.a[1].x = blc_a;
    (*blc_retvar) = blc_s;
    return;
}