
#include <vector.xh>

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  typedef int foo;
  // Can't parameterize a vector with a non-global type
  vector<foo> v = vec<foo> [1, 2, 3];

  printf("%s\n", show(v));

  return 0;
}
