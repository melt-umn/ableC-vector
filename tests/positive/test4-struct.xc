#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

struct foo { int i; float f; };

int main(int argc, char **argv) {
  vector<struct foo> d = vec[(struct foo){42, 3.141f}];
  d.append(d[0]);
  
  if (d[0].i != 42 || d[1].f != 3.141f)
    return 1;
  
  return 0;
}
