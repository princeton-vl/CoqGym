
#include <stdio.h>

int main() {
    int c;
    int prev = 0;
    int nesting = 0;
    int in_string = 0;
    while ((c = getchar()) != EOF) {
        if (prev == '(' && c == '*' && !in_string) {
            ++nesting;
        } else if (prev == '*' && c == ')' && !in_string && nesting > 0) {
            --nesting;
            prev = getchar();
            if (prev == EOF) {
                break;
            }
            continue;
        }
        if (nesting == 0 && prev != 0) {
            putchar(prev);
        }
        prev = c;
        if (c == '"' && nesting == 0) {
            in_string = 1 - in_string;
        }
    }
    if (nesting == 0 && prev != 0 && prev != EOF) {
        putchar(prev);
    }
    return 0;
}
