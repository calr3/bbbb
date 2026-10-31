/*
 * Tooting Terminating Turmites: search for TTT(n, m).
 *
 * A Terminating Turmite (relative-movement TM) has transitions (state, symbol) ->
 * (write, P|T, next state): P proceeds one cell in the current direction, T turns around
 * and moves one cell.  The head starts facing right on a blank tape in state A.
 * An undefined transition halts; the halting step is counted as a step (as for TT).
 * One transition (state, symbol) is the toot transition.  The machine quasihalts at its
 * last toot; its value is the step number (counting from 1) of the last toot.
 * TTT(n, m) is the maximum value over all n-state m-symbol machines with finitely many toots.
 * Tooting on the halting transition gives TT, so TTT(n, m) >= TT(n, m).
 *
 * The program enumerates machines in tree normal form (undefined transitions are filled in
 * when first reached, with the next unused state / symbol only), and for each leaf decides:
 *   - halting (an undefined transition is reached): every transition is used finitely often;
 *   - cycler (exact configuration repeat, Brent) or translated cycler (records on one side with
 *     the same state and the same tape segment over the excursion of the period): the
 *     transitions used in one period are used forever, every other transition never again;
 *   - otherwise a holdout (printed, with its last-use times at L/10 and at L).
 *
 * usage: ttt N M LIMIT [partial-machine]     (partial machine: e.g. 1TB---_1PA0PB)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 6
#define MAXM 6
#define MAXT (MAXN * MAXM)
#define W 256     /* snapshot width for translated cyclers */
#define R 1024    /* records kept per side */

static int N, M;
static long L;
static int tw[MAXN][MAXM], tm[MAXN][MAXM], tn[MAXN][MAXM]; /* tn = -1: undefined */

static uint8_t *tape;  /* index base: head starts at OFF */
static long OFF;
static uint8_t *hist;  /* transition id at each step */
static uint8_t *brentbuf;

static long lastUse[MAXT], lastUseTenth[MAXT];
static int inCycle[MAXT];

/* records */
typedef struct { long step, pos, ext; int q, dir; } Rec;
static Rec recR[R], recL[R];
static uint8_t snapR[R][W], snapL[R][W];
static long nR, nL;

/* results */
static long bestTTT = -1, bestTT = -1, bestQH = -1;
static char bestTTTm[256], bestTTm[256], bestQHm[256];
static int bestTTTt, bestTTt, bestQHt;
static long nodes, nHalt, nCyc, nTCyc, nHold;
static long bestHeur = -1; static char bestHeurm[256]; static int bestHeurt;
static FILE *holdf;

static void mstr(char *out) {
  char *p = out;
  for (int q = 0; q < N; q++) {
    if (q) *p++ = '_';
    for (int s = 0; s < M; s++) {
      if (tn[q][s] < 0) { memcpy(p, "---", 3); p += 3; }
      else { *p++ = '0' + tw[q][s]; *p++ = tm[q][s] ? 'T' : 'P'; *p++ = 'A' + tn[q][s]; }
    }
  }
  *p = 0;
}

static void tname(int id, char *out) { out[0] = 'A' + id / M; out[1] = '0' + id % M; out[2] = 0; }

enum { R_UNDEF, R_CYCLE, R_TCYCLE, R_LIMIT };
static int uq, us; static long ustep, cyc1, cyc2;

static int simulate(void) {
  long pos = OFF, lo = OFF, hi = OFF;
  int q = 0, dir = 1;
  long extR = OFF, extL = OFF; /* min pos since last right record / max since last left */
  nR = nL = 0;
  for (int i = 0; i < N * M; i++) lastUse[i] = 0, lastUseTenth[i] = 0;
  long nextPow = 1, bq = -1, bdir = 0, bpos = 0, blo = 0, bhi = 0, bstep = 0;
  long tenth = L / 10;
  int res = R_LIMIT;
  for (long step = 1; step <= L; step++) {
    int s = tape[pos];
    if (tn[q][s] < 0) { uq = q; us = s; ustep = step; res = R_UNDEF; goto done; }
    int id = q * M + s;
    tape[pos] = tw[q][s];
    if (tm[q][s]) dir = -dir;
    q = tn[q][s];
    pos += dir;
    hist[step] = id;
    lastUse[id] = step;
    if (step == tenth) memcpy(lastUseTenth, lastUse, sizeof lastUse);
    if (pos < extR) extR = pos;
    if (pos > extL) extL = pos;
    if (pos > hi) {
      hi = pos;
      /* new right record */
      long r = nR % R;
      recR[r] = (Rec){step, pos, extR, q, dir};
      for (int k = 0; k < W; k++) snapR[r][k] = tape[pos - k];
      long cummin = pos;
      for (long j = nR - 1; j >= 0 && j > nR - R; j--) {
        Rec *a = &recR[j % R], *b = &recR[(j + 1) % R];
        if (b->ext < cummin) cummin = b->ext;
        if (a->pos < cummin) cummin = a->pos;
        long d = a->pos - cummin;
        if (d >= W) continue;
        if (a->q == q && a->dir == dir && memcmp(snapR[j % R], snapR[r], d + 1) == 0) {
          cyc1 = a->step; cyc2 = step; res = R_TCYCLE; nR++; goto done;
        }
      }
      nR++;
      extR = pos;
    }
    if (pos < lo) {
      lo = pos;
      long r = nL % R;
      recL[r] = (Rec){step, pos, extL, q, dir};
      for (int k = 0; k < W; k++) snapL[r][k] = tape[pos + k];
      long cummax = pos;
      for (long j = nL - 1; j >= 0 && j > nL - R; j--) {
        Rec *a = &recL[j % R], *b = &recL[(j + 1) % R];
        if (b->ext > cummax) cummax = b->ext;
        if (a->pos > cummax) cummax = a->pos;
        long d = cummax - a->pos;
        if (d >= W) continue;
        if (a->q == q && a->dir == dir && memcmp(snapL[j % R], snapL[r], d + 1) == 0) {
          cyc1 = a->step; cyc2 = step; res = R_TCYCLE; nL++; goto done;
        }
      }
      nL++;
      extL = pos;
    }
    /* Brent cycle detection on the exact configuration */
    if (q == bq && dir == bdir && pos == bpos && lo == blo && hi == bhi &&
        memcmp(brentbuf, tape + lo, hi - lo + 1) == 0) {
      cyc1 = bstep; cyc2 = step; res = R_CYCLE; goto done;
    }
    if (step == nextPow) {
      nextPow *= 2;
      bq = q; bdir = dir; bpos = pos; blo = lo; bhi = hi; bstep = step;
      memcpy(brentbuf, tape + lo, hi - lo + 1);
    }
  }
done:
  /* clean the tape (and the snapshot margins) */
  memset(tape + lo - W, 0, hi - lo + 1 + 2 * W);
  if (res == R_CYCLE || res == R_TCYCLE) {
    for (int i = 0; i < N * M; i++) inCycle[i] = 0;
    for (long t = cyc1 + 1; t <= cyc2; t++) inCycle[hist[t]] = 1;
  }
  return res;
}

static void consider(long v, int id, int halting, int haltToot) {
  char ms[256];
  if (v > bestTTT) {
    bestTTT = v; mstr(bestTTTm); bestTTTt = id;
    if (getenv("TTT_PROGRESS")) {
      char t[3]; tname(id, t);
      fprintf(stderr, "new best %ld %s toot %s (node %ld)\n", v, bestTTTm, t, nodes);
    }
  }
  if (haltToot && v > bestTT) { bestTT = v; mstr(bestTTm); bestTTt = id; }
  if (!halting && v > bestQH) { bestQH = v; mstr(bestQHm); bestQHt = id; }
  (void)ms;
}

static int maxState(void) {
  int mx = 0;
  for (int q = 0; q < N; q++) for (int s = 0; s < M; s++) if (tn[q][s] > mx) mx = tn[q][s];
  return mx;
}
static int maxSym(void) {
  int mx = 0;
  for (int q = 0; q < N; q++) for (int s = 0; s < M; s++) if (tn[q][s] >= 0 && tw[q][s] > mx) mx = tw[q][s];
  return mx;
}

static void search(void) {
  nodes++;
  int r = simulate();
  if (r == R_UNDEF) {
    nHalt++;
    int h = uq * M + us;
    consider(ustep, h, 1, 1);
    for (int i = 0; i < N * M; i++) if (i != h) consider(lastUse[i], i, 1, 0);
    int q0 = uq, s0 = us;
    int ms = maxSym() + 1; if (ms > M - 1) ms = M - 1;
    int mq = maxState() + 1; if (mq > N - 1) mq = N - 1;
    for (int w = 0; w <= ms; w++)
      for (int mv = 0; mv < 2; mv++)
        for (int nx = 0; nx <= mq; nx++) {
          tw[q0][s0] = w; tm[q0][s0] = mv; tn[q0][s0] = nx;
          search();
        }
    tn[q0][s0] = -1;
  } else if (r == R_CYCLE || r == R_TCYCLE) {
    if (r == R_CYCLE) nCyc++; else nTCyc++;
    if (getenv("TTT_VERBOSE")) {
      char ms[256]; mstr(ms);
      fprintf(stderr, "%s %s: period from step %ld to %ld (length %ld), in the period:", ms,
              r == R_CYCLE ? "cycler" : "translated cycler", cyc1, cyc2, cyc2 - cyc1);
      for (int i = 0; i < N * M; i++) if (inCycle[i]) { char t[3]; tname(i, t); fprintf(stderr, " %s", t); }
      fprintf(stderr, "\n");
    }
    for (int i = 0; i < N * M; i++) if (!inCycle[i]) consider(lastUse[i], i, 0, 0);
  } else {
    nHold++;
    char ms[256]; mstr(ms);
    for (int i = 0; i < N * M; i++)
      if (lastUse[i] == lastUseTenth[i] && lastUse[i] > bestHeur) {
        bestHeur = lastUse[i]; strcpy(bestHeurm, ms); bestHeurt = i;
      }
    fprintf(holdf, "%s", ms);
    for (int i = 0; i < N * M; i++) {
      char t[3]; tname(i, t);
      fprintf(holdf, " %s:%ld/%ld", t, lastUseTenth[i], lastUse[i]);
    }
    fprintf(holdf, "\n");
  }
}

static int parse(const char *s) {
  for (int q = 0; q < N; q++) for (int k = 0; k < M; k++) tn[q][k] = -1;
  int q = 0, k = 0;
  while (*s) {
    if (*s == '_') { q++; k = 0; s++; continue; }
    if (q >= N || k >= M || strlen(s) < 3) return 0;
    if (s[0] == '-') { tn[q][k] = -1; }
    else {
      tw[q][k] = s[0] - '0'; tm[q][k] = (s[1] == 'T');
      if (s[2] == 'Z' || s[2] == 'H') tn[q][k] = -1; else tn[q][k] = s[2] - 'A';
    }
    k++; s += 3;
  }
  return 1;
}

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: ttt N M LIMIT [partial-machine] [holdout-file]\n"); return 1; }
  N = atoi(argv[1]); M = atoi(argv[2]); L = atol(argv[3]);
  OFF = L + 2 * W + 8;
  tape = calloc(2 * OFF + 1, 1);
  hist = malloc(L + 2);
  brentbuf = malloc(2 * OFF + 1);
  for (int q = 0; q < N; q++) for (int s = 0; s < M; s++) tn[q][s] = -1;
  holdf = argc >= 6 ? fopen(argv[5], "w") : stdout;
  if (argc >= 5 && argv[4][0] == '@') {
    /* a file of partial machines (first word of each line), e.g. holdouts of a shallower run */
    FILE *f = fopen(argv[4] + 1, "r");
    char line[4096];
    while (fgets(line, sizeof line, f)) {
      char *sp = strpbrk(line, " \n"); if (sp) *sp = 0;
      if (!*line) continue;
      parse(line);
      search();
    }
  } else {
    if (argc >= 5 && strcmp(argv[4], "-") != 0) parse(argv[4]);
    search();
  }
  char t[3];
  printf("N=%d M=%d limit=%ld nodes=%ld halting=%ld cyclers=%ld translated=%ld holdouts=%ld\n",
         N, M, L, nodes, nHalt, nCyc, nTCyc, nHold);
  tname(bestTTTt, t); printf("TTT (decided) >= %ld  %s toot %s\n", bestTTT, bestTTTm, t);
  tname(bestTTt, t);  printf("TT  (decided) >= %ld  %s toot %s (halt)\n", bestTT, bestTTm, t);
  tname(bestQHt, t);  printf("TTT non-halting (decided) >= %ld  %s toot %s\n", bestQH, bestQHm, t);
  if (bestHeur >= 0) {
    tname(bestHeurt, t);
    printf("holdouts: largest last use of a transition unused between L/10 and L: %ld  %s toot %s\n",
           bestHeur, bestHeurm, t);
  }
  return 0;
}
