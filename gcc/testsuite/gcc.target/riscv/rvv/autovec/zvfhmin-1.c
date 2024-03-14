/* { dg-do compile } */
/* { dg-options "-march=rv32gcv_zvfhmin -mabi=ilp32d --param riscv-autovec-preference=scalable -fdump-tree-vect-details" } */

void f0 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = -b[i];
}

void f1 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = a[i]+b[i];
}

void f2 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = a[i]-b[i];
}

void f3 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = a[i]*b[i];
}

void f4 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = a[i]/b[i];
}

void f6 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = __builtin_fabs (b[i]);
}

void f7 (_Float16 * __restrict a, _Float16 * __restrict b, int n)
{
  for (int i = 0; i < n; i++)
    a[i] = __builtin_sqrtf (b[i]);
}

/* We can't enable FP16 NEG/PLUS/MINUS/MULT/DIV/ABS/SQRTF auto-vectorization
   when -march="*zvfhmin*" because the min variant of the extension only
   provides loads, stores and conversions.  */
/* { dg-final { scan-tree-dump-times "vectorized 1 loops in function" 0 "vect" } } */
