#include <vector.xh>

struct empty {};

int main() {
  with_arena ar {
    new vector<struct empty>(5);
  }
}
