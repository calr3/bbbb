#!/usr/bin/env python3
"""Exploration (not part of the proof): estimate g for the holdouts of enumerate.py by simulating
N steps: a value counts as repeated forever if it occurs 3 times among the intervals ending in the
last tenth of the run, and estimates above N/8 are dropped (growing bouncers give false hits that
scale with N; check candidates with recheck.py at several N).

Usage: holdouts.py NS NSYM N   (reads holdouts_<NS>x<NSYM>.txt)
"""
import sys, collections, itertools
import numpy as np
NS, NSYM = int(sys.argv[1]), int(sys.argv[2]); N = int(sys.argv[3])
T = NS * NSYM
names = open(f'holdouts_{NS}x{NSYM}.txt').read().split()
def parse(s):
    M = [None] * T
    for st, part in enumerate(s.split('_')):
        for b in range(NSYM):
            t = part[3*b:3*b+3]
            if t != '---': M[st*NSYM+b] = (int(t[0]), 1 if t[1] == 'R' else -1, 'ABCDE'.index(t[2]))
    return M
def run(M, n):
    tape = collections.defaultdict(int); h = 0; s = 0; labs = []
    for _ in range(n):
        b = tape[h]; t = M[s*NSYM+b]
        if t is None: break
        labs.append(s*NSYM+b); w, d, q = t; tape[h] = w; h += d; s = q
    return np.array(labs)
Bmat = np.array([[(m >> t) & 1 for t in range(T)] for m in range(1 << T)])  # (64, T)
tn = lambda t: 'ABCDE'[t // NSYM] + str(t % NSYM)
res = []
for nm in names:
    labs = run(parse(nm), N)
    onehot = np.eye(T, dtype=np.int64)[labs]; cs = np.vstack([np.zeros(T, np.int64), np.cumsum(onehot, 0)])
    best = (0, None)
    for o in range(1, 1 << T):
        Oset = [t for t in range(T) if (o >> t) & 1]
        boops = np.nonzero(np.isin(labs, Oset))[0]
        if len(boops) < 8: continue
        a, b = boops[:-1], boops[1:]
        cnt = cs[b] - cs[a + 1]            # (nint, T) counts strictly between
        vals = cnt @ Bmat.T                # (nint, 64)
        late = b > 9 * len(labs) // 10
        for bi in range(1 << T):
            v = vals[:, bi]
            u, c = np.unique(v[late], return_counts=True)
            rep = u[c >= 3]
            if len(rep) == 0: continue
            idx = np.nonzero(np.isin(v, rep))[0][0]
            g = b[idx] + 1
            if g > len(labs) // 8: continue
            if g > best[0]: best = (g, ([tn(t) for t in range(T) if (bi >> t) & 1], [tn(t) for t in Oset]))
    res.append((best[0], nm, best[1]))
res.sort(reverse=True)
for r in res[:15]: print(r)
