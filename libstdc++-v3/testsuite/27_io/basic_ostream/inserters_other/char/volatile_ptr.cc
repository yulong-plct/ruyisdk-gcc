// { dg-options "-fno-inline" }
// { dg-do run { target c++23 } }

#include <iostream>

int main()
{
  int i = 0;
  volatile void* p = &i;
  std::cout << p << std::endl;
}
