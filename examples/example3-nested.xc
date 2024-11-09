#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

arena_t ar;
allocate_using arena ar;

int main(int argc, char **argv) {
  ar = arena_create();

  vector<vector<string>> elems = {{str("abcd")}};

  for (int i = 1; i < 7; i++) {
    elems.append(vec[str("Hello"), str("World"), str(i), show(elems[i - 1])]);
  }

  printf("%s\n", show(elems).text);

  return 0;
}
