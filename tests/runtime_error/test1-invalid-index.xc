#include <vector.xh>

#include <stdio.h>
#include <stdlib.h>

int main() {
  with_arena ar {
    vector<int> a = vec[1, 2, 3];
    int i = a[100];
  }
  return 0;
}
