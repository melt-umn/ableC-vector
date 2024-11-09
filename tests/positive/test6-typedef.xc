#include <vector.xh>
#include <string.xh>

typedef vector<int> foo_t;

int main() {
  with_arena ar {
    foo_t f = new vector<int>(4, 1);
    printf("%s\n", show(f).text);
    return f != vec[1, 1, 1, 1];
  }
}
