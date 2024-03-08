/* { dg-do run { target { riscv_vector } } } */
/* { dg-additional-options "-std=c99 -fno-vect-cost-model --param=riscv-autovec-preference=fixed-vlmax" } */

#include "vsub-template.h"

#include <assert.h>

#define SZ 512

#define RUN(TYPE,VAL)				\
  TYPE a##TYPE[SZ];				\
  TYPE b##TYPE[SZ];	  			\
  for (int i = 0; i < SZ; i++)			\
  {                             		\
    a##TYPE[i] = 999;           		\
    b##TYPE[i] = VAL;           		\
  }                             		\
  vsub_##TYPE (a##TYPE, a##TYPE, b##TYPE, SZ);	\
  for (int i = 0; i < SZ; i++)			\
    assert (a##TYPE[i] == 999 - VAL);

#define RUN2(TYPE,VAL)				\
  TYPE as##TYPE[SZ];				\
  for (int i = 0; i < SZ; i++)			\
    as##TYPE[i] = 999;            		\
  vsubs_##TYPE (as##TYPE, as##TYPE, VAL, SZ);	\
  for (int i = 0; i < SZ; i++)			\
    assert (as##TYPE[i] == 999 - VAL);

#define RUN3(TYPE)				\
  TYPE as2##TYPE[SZ];				\
  for (int i = 0; i < SZ; i++)			\
    as2##TYPE[i] = i * 33 - 779;            	\
  vsubi_##TYPE (as2##TYPE, as2##TYPE, SZ);	\
  for (int i = 0; i < SZ; i++)			\
    assert (as2##TYPE[i] == (TYPE)(-16 - (i * 33 - 779)));

#define RUN4(TYPE)				\
  TYPE as3##TYPE[SZ];				\
  for (int i = 0; i < SZ; i++)			\
    as3##TYPE[i] = i * -17 + 667;            	\
  vsubi2_##TYPE (as3##TYPE, as3##TYPE, SZ);	\
  for (int i = 0; i < SZ; i++)			\
    assert (as3##TYPE[i] == (TYPE)(15 - (i * -17 + 667)));

#define RUN_ALL()	\
 RUN(int16_t, 1)	\
 RUN(uint16_t, 2)	\
 RUN(int32_t, 3)	\
 RUN(uint32_t, 4)	\
 RUN(int64_t, 5)	\
 RUN(uint64_t, 6)	\
 RUN2(int16_t, 7)	\
 RUN2(uint16_t, 8)	\
 RUN2(int32_t, 9)	\
 RUN2(uint32_t, 10)	\
 RUN2(int64_t, 11)	\
 RUN2(uint64_t, 12)	\
 RUN3(int16_t)		\
 RUN3(uint16_t)		\
 RUN3(int32_t)		\
 RUN3(uint32_t)		\
 RUN3(int64_t)		\
 RUN3(uint64_t)		\
 RUN4(int16_t)		\
 RUN4(uint16_t)		\
 RUN4(int32_t)		\
 RUN4(uint32_t)		\
 RUN4(int64_t)		\
 RUN4(uint64_t)

int main ()
{
  RUN_ALL()
}
