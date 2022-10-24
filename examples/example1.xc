#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

int main(int argc, char **argv) {
  vector<int> a = vec[1, 2, 3];
  printf("a: %s\n", show(a).text);
  vector<int> b = vec(GC_malloc, GC_realloc) [4, 5, 6];
  printf("b: %s\n", show(b).text);
  vector<int> c = a + b;
  printf("c: %s\n", show(c).text);
  printf("a: %s\n", show(a).text);
  a += b;
  printf("a: %s\n", show(a).text);
  b[1] += 7;
  b.append(6);
  printf("b: %s\n", show(b).text);
  vector<int> d = b.copy();
  b[2] = 7;
  printf("b: %s\n", show(b).text);
  printf("d: %s\n", show(d).text);
  vector<int> e = b;
  e += a;
  printf("e: %s\n", show(e).text);
  e.extend(a);
  printf("e: %s\n", show(e).text);
  e.append(42);
  e.insert(2, 23);
  printf("e: %s\n", show(e).text);
  e.extend(e);
  printf("e: %s\n", show(e).text);
  vector<int> f = new vector<int>(4, 17);
  printf("f: %s\n", show(f).text);
  vector<int> g = {1, 2, 3, 4, 5};
  printf("g: %s\n", show(g).text);
  
  if (a != c)
    return 1;
  if (a == b)
    return 2;
  if (b[1] != 12)
    return 3;
  if (b[3] != 6)
    return 4;
  if (b.length != 4)
    return 5;
  if (b == d)
    return 6;
  if (e[20] != 23)
    return 7;
  if (f[2] != 17)
    return 8;
  if (g[2] != 3)
    return 9;

  return 0;
}
