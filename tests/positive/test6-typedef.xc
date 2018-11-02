#include <vector.xh>
#include <string.xh>
#include <gc.h>

typedef vector<int> foo_t;

int main() {
  foo_t f = new foo_t(4, 1);
  printf("%s\n", show(f).text);
  return f != vec<int>[1, 1, 1, 1];
}
