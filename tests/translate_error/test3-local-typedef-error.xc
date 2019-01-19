#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

int main(int argc, char **argv) {
  typedef int foo;
  // Can't parameterize a vector with a non-global type
  vector<foo> v = vec[1, 2, 3];

  printf("%s\n", show(v));

  return 0;
}
