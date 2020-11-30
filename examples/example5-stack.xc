#include <vector.xh>

#include <assert.h>
#include <gc.h>

int main(void) {
  vector<int> stack = vec[1, 2, 3];
  assert(stack.pop() == 3);
  assert(stack.pop() == 2);
  stack.append(4);
  assert(stack.pop() == 4);
  stack.append(5);
  stack.append(6);
  assert(stack.pop() == 6);
  assert(stack.pop() == 5);
  assert(stack.pop() == 1);
  return 0;
}
