#!/usr/bin/env python3
"""Rough classification of the distinct BBBB(3) holdouts by tape growth: the ratio of visited widths at
steps 80000 and 20000 is about 4 for translated cyclers, 2 for bouncers (quadratic time), close to 1
for counters (exponential time)."""
import collections, sys
sys.path.insert(0, '.'); sys.path.insert(0, '..')
import gen3

def parse(nm):
    P = []
    for part in nm.split('_'):
        for b in range(2):
            t = part[3*b:3*b+3]
            if t == '---': P.append(None); continue
            P.append(1 + 6*int(t[0]) + (0 if t[1] == 'R' else 3) + 'ABC'.index(t[2]))
    return P

names = sorted({gen3.canon(parse(l.strip())) for l in open('holdouts3_full.txt')})
types = collections.Counter(); out = []
for nm in names:
    M = gen3.tomach(parse(nm))
    tape = collections.defaultdict(int); h = 0; s = 0; lo = hi = 0; w = {}
    for t in range(1, 80001):
        b = tape[h]; x = M[(s, b)]
        if x is None: break
        ww, d, q = x; tape[h] = int(ww); h += 1 if d == 'R' else -1; s = q
        lo = min(lo, h); hi = max(hi, h)
        if t in (20000, 80000): w[t] = hi - lo + 1
    r = w[80000] / w[20000]
    ty = 'linear' if r > 3 else 'sqrt' if r > 1.6 else 'slow'
    types[ty] += 1; out.append((ty, round(r, 2), w[80000], nm))
print(dict(types))
with open('holdout_types.txt', 'w') as f:
    for o in sorted(out): f.write(f'{o[0]} {o[1]} {o[2]} {o[3]}\n')
