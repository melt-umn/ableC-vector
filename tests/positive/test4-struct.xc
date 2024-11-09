#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

struct foo { int i; float f; };

int main(int argc, char **argv) {
  with_arena ar {
    vector<struct foo> d = vec[(struct foo){42, 3.141f}];
    d.append(d[0]);

    printf("d: %s\n", show(d).text);
    
    if (d[0].i != 42 || d[1].f != 3.141f)
      return 1;

    vector<struct foo> e = {{5, 2.27f}, {4, 5.32f}};
    e.extend(d);
    
    printf("e: %s\n", show(e).text);

    if (e[0].i != 5 || e[1].f != 5.32f)
      return 2;
  }
  
  return 0;
}
