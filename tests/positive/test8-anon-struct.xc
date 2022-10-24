#include <vector.xh>
#include <gc.h>

typedef struct { int x; } foo_t;

int main() {
  new vector<foo_t>(5)[3].x;
  
  new vector<struct { int x; }>(5)[3].x;
}
