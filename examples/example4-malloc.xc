#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  vector<int> a = vec(malloc, realloc, free) [1, 2, 3];
  printf("a: %s\n", show(a).text);
  vector<int> b = vec(malloc, realloc, free) [4, 5, 6];
  printf("b: %s\n", show(b).text);
  vector<int> c = a + b;
  printf("c: %s\n", show(c).text);
  printf("a: %s\n", show(a).text);
  vector<int> old_a = a;
  a += b;
  delete old_a;
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
  
  delete a;
  delete b;
  delete c;
  delete d;
  delete e;
  
  return 0;
}
