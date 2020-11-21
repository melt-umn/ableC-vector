#include <vector.xh>
#include <gc.h>

struct empty {};

int main() {
  new vector<struct empty>(5);
}
