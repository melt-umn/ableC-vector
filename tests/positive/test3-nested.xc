#include <vector.xh>
#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>

int main(int argc, char **argv) {
  vector<vector<string>> elems = vec[vec[str("abcd")]];

  for (int i = 1; i < 7; i++) {
    elems.append(vec[str("Hello"), str("World"), str(i), show(elems[i - 1])]);
  }

  printf("%s\n", show(elems).text);

  if (elems != vec[vec[str("abcd")], vec[str("Hello"), str("World"), str("1"), str("[\"abcd\"]")], vec[str("Hello"), str("World"), str("2"), str("[\"Hello\", \"World\", \"1\", \"[\\\"abcd\\\"]\"]")], vec[str("Hello"), str("World"), str("3"), str("[\"Hello\", \"World\", \"2\", \"[\\\"Hello\\\", \\\"World\\\", \\\"1\\\", \\\"[\\\\\\\"abcd\\\\\\\"]\\\"]\"]")], vec[str("Hello"), str("World"), str("4"), str("[\"Hello\", \"World\", \"3\", \"[\\\"Hello\\\", \\\"World\\\", \\\"2\\\", \\\"[\\\\\\\"Hello\\\\\\\", \\\\\\\"World\\\\\\\", \\\\\\\"1\\\\\\\", \\\\\\\"[\\\\\\\\\\\\\\\"abcd\\\\\\\\\\\\\\\"]\\\\\\\"]\\\"]\"]")], vec[str("Hello"), str("World"), str("5"), str("[\"Hello\", \"World\", \"4\", \"[\\\"Hello\\\", \\\"World\\\", \\\"3\\\", \\\"[\\\\\\\"Hello\\\\\\\", \\\\\\\"World\\\\\\\", \\\\\\\"2\\\\\\\", \\\\\\\"[\\\\\\\\\\\\\\\"Hello\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"World\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"1\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"[\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"abcd\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"]\\\\\\\\\\\\\\\"]\\\\\\\"]\\\"]\"]")], vec[str("Hello"), str("World"), str("6"), str("[\"Hello\", \"World\", \"5\", \"[\\\"Hello\\\", \\\"World\\\", \\\"4\\\", \\\"[\\\\\\\"Hello\\\\\\\", \\\\\\\"World\\\\\\\", \\\\\\\"3\\\\\\\", \\\\\\\"[\\\\\\\\\\\\\\\"Hello\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"World\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"2\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\"[\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"Hello\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"World\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"1\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\", \\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"[\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"abcd\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"]\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\"]\\\\\\\\\\\\\\\"]\\\\\\\"]\\\"]\"]")]])
    return 1;
  
  return 0;
}
