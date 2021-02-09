#include <string.h>

#include "blech.h"

#include "returnsArrayFromExternFunction.ext.h"

void rrr_impl (const blc_bool blc_a,
                     struct blc_returnsArrayFromExternFunction_Foo blc_lala[3],
                     struct blc_returnsArrayFromExternFunction_Foo blc_retvar[3]) {
    struct blc_returnsArrayFromExternFunction_Foo blc_s;
    memset(&(blc_s), 0, sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    blc_s.i = -7;
    blc_s.j = 3.420000;
    blc_s.a[0].s1 = 8;
    blc_s.a[0].s2 = -9.000000;
    blc_s.a[1].s1 = 11;
    blc_s.a[1].s2 = -22.000000;
    struct blc_returnsArrayFromExternFunction_Foo tmpLiteral_0[3];
    memset(tmpLiteral_0,
           0,
           3 * sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    tmpLiteral_0[0] = blc_s;
    tmpLiteral_0[1].j = 18.700000;
    tmpLiteral_0[2].j = 18.700000;
    memcpy(blc_retvar,
           tmpLiteral_0,
           3 * sizeof(struct blc_returnsArrayFromExternFunction_Foo));
    return;
}