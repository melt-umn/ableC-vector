#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

int main(int argc, char **argv) {
  vector<vector<string>> elems = {{str("abcd")}};

  for (int i = 1; i < 7; i++) {
    elems.append(vec[str("Hello"), str("World"), str(i), show(elems[i - 1])]);
  }

  printf("%s\n", show(elems).text);

  return 0;
}
