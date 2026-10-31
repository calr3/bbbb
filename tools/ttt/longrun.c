/* longrun MACHINE STEPS: plain simulation tracking the last use of each transition and the
   tape extent (for long checks of holdouts).  Same conventions as ttt.c. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
  const char *s = argv[1]; long L = atol(argv[2]);
  int tw[8][8], tm[8][8], tn[8][8], N = 0, M = 0, k = 0;
  for (; *s; ) { if (*s == '_') { N++; M = k; k = 0; s++; continue; }
    tw[N][k] = s[0]-'0'; tm[N][k] = s[1]=='T'; tn[N][k] = s[0]=='-' ? -1 : s[2]-'A'; k++; s += 3; }
  N++; if (!M) M = k;
  long W = 4000000; uint8_t *tape = calloc(2*W, 1); long pos = W, lo = W, hi = W; int q = 0, d = 1;
  long last[64] = {0};
  for (long t = 1; t <= L; t++) {
    int c = tape[pos];
    if (tn[q][c] < 0) { printf("halt at %ld\n", t); break; }
    last[q*M+c] = t; tape[pos] = tw[q][c]; if (tm[q][c]) d = -d; q = tn[q][c]; pos += d;
    if (pos < lo) lo = pos; if (pos > hi) hi = pos;
    if (pos <= 0 || pos >= 2*W-1) { printf("tape overflow at %ld\n", t); break; }
  }
  printf("%s extent %ld..%ld:", argv[1], lo-W, hi-W);
  for (int i = 0; i < N*M; i++) printf(" %c%d:%ld", 'A'+i/M, i%M, last[i]);
  printf("\n"); return 0;
}
