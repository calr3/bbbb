/* growthc FILE: for each machine (first word of each line), tape width at steps 2.5e5, 1e6, 4e6
   and the ratios; prints class: lin (ratio>3), sqrt (1.6..3), mid (1.25..1.6), slow (<1.25) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv) {
  FILE *f = fopen(argv[1], "r"); char line[4096];
  long W = 5000000; uint8_t *tape = calloc(2*W, 1);
  while (fgets(line, sizeof line, f)) {
    char *sp = strpbrk(line, " \n"); if (sp) *sp = 0;
    int tw[8][8], tm[8][8], tn[8][8], N = 0, M = 0, k = 0; const char *s = line;
    for (; *s; ) { if (*s == '_') { N++; M = k; k = 0; s++; continue; }
      tw[N][k] = s[0]-'0'; tm[N][k] = s[1]=='T'; tn[N][k] = s[0]=='-' ? -1 : s[2]-'A'; k++; s += 3; }
    N++; if (!M) M = k;
    long pos = W, lo = W, hi = W; int q = 0, d = 1; long w1 = 0, w2 = 0, w3 = 0;
    for (long t = 1; t <= 4000000; t++) {
      int c = tape[pos]; if (tn[q][c] < 0) break;
      tape[pos] = tw[q][c]; if (tm[q][c]) d = -d; q = tn[q][c]; pos += d;
      if (pos < lo) lo = pos; if (pos > hi) hi = pos;
      if (t == 250000) w1 = hi-lo+1; if (t == 1000000) w2 = hi-lo+1; if (t == 4000000) w3 = hi-lo+1;
    }
    memset(tape + lo, 0, hi - lo + 1);
    double r = (double)w3 / w2;
    const char *c = r > 3 ? "lin" : r > 1.6 ? "sqrt" : r > 1.25 ? "mid" : "slow";
    printf("%s %.2f %ld %ld %ld %s\n", c, r, w1, w2, w3, line);
  }
  return 0;
}
