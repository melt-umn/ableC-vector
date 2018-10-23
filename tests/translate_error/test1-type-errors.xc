#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

struct foo { int i; float f; };

int main(int argc, char **argv) {
  vector<int> a = vec<float> [1, 2, 3]; // Incompatible vector type assignment
  printf("a: %s\n", show(a));
  vector<int> b = vec<int> [4, 5, 6];
  printf("b: %s\n", show(b));
  vector<int> c = a + b;
  printf("c: %s\n", show(c));
  a += b;
  printf("a: %s\n", show(a));
  b[1] += 7;
  b[3] = 6;
  printf("b: %s\n", show(b));

  c.append("a"); // Content type is int, not char *
  c.insert("a", 3.2); // Insertion index must be an integer, invalid type inserted
  c.extend(3); // Extend must take another vector
  str(c); // str(vector) is not defined

  vector<struct foo> d = vec<struct foo> [(struct foo){42, 3.141f}];
  show(d); // show(struct foo) is not defined
  d != d; // == for struct foo is not defined
  
  return 0;
}
