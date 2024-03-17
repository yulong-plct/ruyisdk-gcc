/* { dg-do compile } */
/* { dg-options "-O3 -march=rv64gcv -mabi=lp64d --param=riscv-autovec-preference=fixed-vlmax" } */

int a, b, c, e;
short d[7][7] = {};
int foo() {
  short f;
  c = 0;
  for (; c <= 6; c++) {
    e |= d[c][c] & 1;
    b &= f & 3;
  }
  return a;
}

/* { dg-final { scan-assembler-times {vsetvli\s+[a-x0-9]+,\s*zero} 1 } } */
