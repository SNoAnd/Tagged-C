#include <stdio.h>

int strlen(char *p) {
  int c = 0;
  while (*p != '\0') {
    p++;
    c++;
  }
  return c;
}

char c[200];


int main() {
  char *p = fgets(c,2,stdin);
  printf("%p %p %d %s\n",c, p,strlen(p), p);
}
    
