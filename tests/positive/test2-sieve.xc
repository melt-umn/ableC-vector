#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

vector<int> sieve(int n, arena_t ar) {
  allocate_using arena ar;

  vector<int> ints = new vector<int>(n);
  for (int i = 0; i < n; i++)
    ints[i] = i;

  vector<int> results = vec<int>[];
  for (int i = 2; i < n; i++) {
    if (ints[i] != -1) {
      for (int j = i * 2; j < n; j += i) {
        ints[j] = -1;
      }
      results.append(i);
    }
  }

  return results;
}

int main(int argc, char **argv) {
  with_arena ar {
    vector<int> result = sieve(100, ar);
    printf("sieve(100) = %s\n", show(result).text);
    if (result != vec[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97])
      return 1;
  }
  
  return 0;
}
