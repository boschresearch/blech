#include <string.h>

#include "blech.h"

#include "blech/returnsArrayFromExternFunction.h"

void blc_returnsArrayFromExternFunction_rrr (const blc_bool blc_a,
                     struct blc_returnsArrayFromExternFunction_Foo blc_lala[3],
                     struct blc_returnsArrayFromExternFunction_Foo blc_retvar[3]) {
    struct blc_returnsArrayFromExternFunction_Foo blc_s;
    memset(&(blc_s), 0, sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    blc_s.i = -7;
    blc_s.j = 3.420000f;
    blc_s.a[0].s1 = 8;
    blc_s.a[0].s2 = -9.000000f;
    blc_s.a[1].s1 = 11;
    blc_s.a[1].s2 = -22.000000f;
    struct blc_returnsArrayFromExternFunction_Foo tmpLiteral_0[3];
    memset(tmpLiteral_0,
           0,
           3 * sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    tmpLiteral_0[0] = blc_s;
    tmpLiteral_0[1].j = 18.700000f;
    tmpLiteral_0[2].j = 18.700000f;
    memcpy(blc_retvar,
           tmpLiteral_0,
           3 * sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    return;
}