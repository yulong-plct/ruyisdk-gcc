/* { dg-do compile } */
/* { dg-options "-march=rv64gcv_zvfh_zvl4096b -mabi=lp64d -O3 -fno-schedule-insns -fno-schedule-insns2 --param=riscv-autovec-lmul=m8 -ffast-math" } */

#include "def.h"
#include <math.h>

DEF_SGNJX_VV (sgnj, 1, float, copysignf)
DEF_SGNJX_VV (sgnj, 2, float, copysignf)
DEF_SGNJX_VV (sgnj, 4, float, copysignf)
DEF_SGNJX_VV (sgnj, 8, float, copysignf)
DEF_SGNJX_VV (sgnj, 16, float, copysignf)
DEF_SGNJX_VV (sgnj, 32, float, copysignf)
DEF_SGNJX_VV (sgnj, 64, float, copysignf)
DEF_SGNJX_VV (sgnj, 128, float, copysignf)
DEF_SGNJX_VV (sgnj, 256, float, copysignf)
DEF_SGNJX_VV (sgnj, 512, float, copysignf)
DEF_SGNJX_VV (sgnj, 1024, float, copysignf)

DEF_SGNJX_VV (sgnj, 1, double, copysign)
DEF_SGNJX_VV (sgnj, 2, double, copysign)
DEF_SGNJX_VV (sgnj, 4, double, copysign)
DEF_SGNJX_VV (sgnj, 8, double, copysign)
DEF_SGNJX_VV (sgnj, 16, double, copysign)
DEF_SGNJX_VV (sgnj, 32, double, copysign)
DEF_SGNJX_VV (sgnj, 64, double, copysign)
DEF_SGNJX_VV (sgnj, 128, double, copysign)
DEF_SGNJX_VV (sgnj, 256, double, copysign)
DEF_SGNJX_VV (sgnj, 512, double, copysign)

/* { dg-final { scan-assembler-times {vfsgnjx\.vv\s+v[0-9]+,\s*v[0-9]+,\s*v[0-9]+} 19 } } */
/* { dg-final { scan-assembler-not {csrr} } } */
