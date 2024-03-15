/* { dg-do compile } */
/* { dg-options "-march=rv64gcv_zvfh -mabi=lp64d -O3 -ftree-vectorize -fno-vect-cost-model -ffast-math -fno-schedule-insns -fno-schedule-insns2" } */
/* { dg-final { check-function-bodies "**" "" } } */

#include "test-math.h"

/*
** test__Float16___builtin_ceilf16:
**   frrm\s+[atx][0-9]+
**   ...
**   fsrmi\s+3
**   ...
**   vsetvli\s+[atx][0-9]+,\s*zero,\s*e16,\s*m1,\s*ta,\s*mu
**   vfabs\.v\s+v[0-9]+,\s*v[0-9]+
**   ...
**   vmflt\.vv\s+v0,\s*v[0-9]+,\s*v[0-9]+
**   ...
**   vfcvt\.x\.f\.v\s+v[0-9]+,\s*v[0-9]+,\s*v0\.t
**   ...
**   vfcvt\.f\.x\.v\s+v[0-9]+,\s*v[0-9]+,\s*v0\.t
**   vfsgnj\.vv\s+v[0-9]+,v[0-9]+,v[0-9]+
**   ...
**   fsrm\s+[atx][0-9]+
**   ...
*/
TEST_CEIL(_Float16, __builtin_ceilf16)
