#!/usr/bin/env python3
"""Exploration (not part of the proof): every machine with NS states and NSYM symbols, enumerated
lazily (a transition is defined only when the run first reaches it, the first move is to the right
by mirror symmetry), simulated for N steps.  Machines whose transitions become periodic get their
exact g for every beep and boop set (heuristic periodicity test); the others are written to
holdouts_<NS>x<NSYM>.txt.

Usage: enumerate.py NS NSYM [N] [skip]   (skip: do not estimate holdouts here, use holdouts.py)
"""
import sys, itertools, collections
NS, NSYM = int(sys.argv[1]), int(sys.argv[2])
N = int(sys.argv[3]) if len(sys.argv) > 3 else 3000
T = NS * NSYM  # transitions, label = s*NSYM+b

def run(M, n):
    """simulate; return (labels, None) or (labels, (s,b)) at an undefined transition"""
    tape = collections.defaultdict(int); h = 0; s = 0; labs = []
    for _ in range(n):
        b = tape[h]; t = M[s * NSYM + b]
        if t is None: return labs, (s, b)
        labs.append(s * NSYM + b); w, d, q = t; tape[h] = w; h += d; s = q
    return labs, None

def periodic(labs):
    """eventually periodic labels (heuristic): minimal (t0, p) with the tail repeating"""
    n = len(labs); tail = labs[n // 2:]
    for p in range(1, n // 8):
        if all(tail[i] == tail[i + p] for i in range(len(tail) - p)):
            t0 = n // 2
            while t0 > 0 and labs[t0 - 1] == labs[t0 - 1 + p]: t0 -= 1
            return t0, p
    return None

subsets = [frozenset(c) for r in range(T + 1) for c in itertools.combinations(range(T), r)]

def g_periodic(labs, t0, p, B, O):
    end = t0 + 3 * p + 2
    boops = [k for k in range(end) if labs[k] in O]
    if not any(t0 <= k < t0 + p for k in boops): return None
    per = set(); vals = []
    for a, b in zip(boops, boops[1:]):
        v = sum(1 for k in range(a + 1, b) if labs[k] in B); vals.append((b, v))
        if t0 <= a < t0 + p: per.add(v)
    for b, v in vals:
        if v in per: return b + 1

def g_heur(labs, B, O):
    boops = [k for k, l in enumerate(labs) if l in O]
    pre = [0]
    for l in labs: pre.append(pre[-1] + (l in B))
    ints = [(b + 1, pre[b] - pre[a + 1]) for a, b in zip(boops, boops[1:])]
    n = len(labs); c = collections.Counter(v for e, v in ints if e > n // 2)
    late = {v for v, k in c.items() if k >= 3}
    return next((e for e, v in ints if v in late), None)

best = 0; champs = []; holds = []; nleaf = 0; nper = 0
def consider(M):
    global best, champs, nleaf, nper
    nleaf += 1
    labs, _ = run(M, N)
    pr = periodic(labs)
    if pr is None:
        holds.append(M); return
    nper += 1
    t0, p = pr
    for O in subsets:
        if not O: continue
        # B-free bound: second boop at or after t0
        fb = [k for k in range(t0, t0 + 2 * p + 1) if labs[k] in O]
        if not fb or fb[0] >= t0 + p: continue
        if fb[1] + 1 < best: continue
        for B in subsets:
            g = g_periodic(labs, t0, p, B, O)
            if g is None: continue
            if g > best: best = g; champs = []
            if g == best and len(champs) < 50: champs.append((M, sorted(B), sorted(O)))

def opts(nused):
    out = []
    for w in range(NSYM):
        for d in (1, -1):
            for q in range(min(nused + 1, NS)):
                out.append((w, d, q))
    return out

def search(M, nused, first):
    labs, und = run(M, N)
    if und is None:
        consider(M); return
    s, b = und
    for o in opts(nused):
        if first and o[1] == -1: continue  # mirror symmetry
        M2 = list(M); M2[s * NSYM + b] = o
        search(M2, max(nused, o[2] + 1), False)
    # (choosing halt gives g = infinity: skipped)

search([None] * T, 1, True)
print(f"{NS} states {NSYM} symbols: leaves {nleaf}, periodic {nper}, holdouts {len(holds)}")
print("best periodic g", best)
def name(M):
    def tt(x):
        if x is None: return '---'
        w, d, q = x; return f"{w}{'R' if d == 1 else 'L'}{'ABCDE'[q]}"
    return '_'.join(''.join(tt(M[s * NSYM + b]) for b in range(NSYM)) for s in range(NS))
def tn(t): return 'ABCDE'[t // NSYM] + str(t % NSYM)
for M, B, O in champs[:15]: print(' ', name(M), 'beep', [tn(t) for t in B], 'boop', [tn(t) for t in O])
# holdouts: heuristic g over all B, O
open(f"holdouts_{NS}x{NSYM}.txt", "w").write("".join(name(M) + "\n" for M in holds))
if len(sys.argv) > 4: sys.exit()
hb = 0; hc = []
for M in holds:
    labs, _ = run(M, 30000)
    for O in subsets:
        if not O: continue
        for B in subsets:
            g = g_heur(labs, B, O)
            if g and g > hb: hb = g; hc = [(name(M), [tn(t) for t in B], [tn(t) for t in O])]
            elif g and g == hb and len(hc) < 10: hc.append((name(M), [tn(t) for t in B], [tn(t) for t in O]))
print("holdouts: heuristic best g", hb)
for x in hc: print(' ', x)
