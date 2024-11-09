#include <vector.xh>

typedef struct { int x; } foo_t;

int main() {
  with_arena ar {
    new vector<foo_t>(5)[3].x;
    
    //new vector<struct { int x; }>(5)[3].x;
  }
}
