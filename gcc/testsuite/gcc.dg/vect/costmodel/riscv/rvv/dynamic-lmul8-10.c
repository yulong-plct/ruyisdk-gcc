/* { dg-do compile } */
/* { dg-options "-march=rv64gcv -mabi=lp64d -O3 -ftree-vectorize --param riscv-autovec-lmul=dynamic -fdump-tree-vect-details" } */

#include <stdint-gcc.h>

int
foo (int *x, int n, int res)
{
  for (int i = 0; i < n; ++i)
    {
      res += x[i * 2];
      res += x[i * 2 + 1];
    }
  return res;
}

/* { dg-final { scan-assembler {e32,m8} } } */
/* { dg-final { scan-assembler-times {csrr} 1 } } */
/* { dg-final { scan-tree-dump "Maximum lmul = 8" "vect" } } */
/* { dg-final { scan-tree-dump-not "Maximum lmul = 4" "vect" } } */
/* { dg-final { scan-tree-dump-not "Maximum lmul = 2" "vect" } } */
/* { dg-final { scan-tree-dump-not "Maximum lmul = 1" "vect" } } */
