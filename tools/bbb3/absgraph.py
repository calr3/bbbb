"""Exact Python port of `Bbbb/Bbb/Tail.lean`, `Abs.lean` (abstract windows) and certificate search
for `Rec.lean` (closed node set + lexicographic ranks per state).

Kinds: 'b' blank, 'n' nonblank, 'y' any, ('A', i), ('W', j).  A side is (a, w) (tuples of 0/1).
Effects: 'd' (dec), 'l' (le), 'y' (any)."""
import sys, os, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from gen import wrun, WINIT, BLANK

def get(l, i):
    return l[i] if 0 <= i < len(l) else None

def pop(sp, k):
    a, w = sp
    if k == 'b': return [(0, 'b', False)]
    if k == 'y': return [(0, 'y', False), (1, 'y', False)]
    if k == 'n': return [(1, 'b', True), (1, 'n', True), (0, 'n', True)]
    t, i = k
    if t == 'W':
        c = get(w, i)
        if c is None: return [(0, 'b', False)]
        return [(c, ('W', i + 1), 1 in w[i:])]
    c = get(a, i)
    if c is None: return [(0, 'y', False), (1, 'y', False)]
    d = 1 in (a[i:] + w)
    if i + 1 < len(a): return [(c, ('A', i + 1), d)]
    return [(c, ('A', 0), d), (c, ('W', 0), d)]

def push(sp, c, k):
    a, w = sp
    if k == 'n': return 'n'
    if k == 'y': return 'n' if c else 'y'
    if k == 'b':
        if not c: return 'b'
        if w: return ('W', len(w) - 1) if w[-1] == c else 'n'
        if a: return ('A', len(a) - 1) if a[-1] == c else 'n'
        return 'n'
    t, i = k
    if t == 'W':
        if i > 0 and get(w, i - 1) == c: return ('W', i - 1)
        if i == 0 and a and a[-1] == c: return ('A', len(a) - 1)
        return 'n' if c else 'y'
    if i > 0 and get(a, i - 1) == c: return ('A', i - 1)
    if i == 0 and a and a[-1] == c: return ('A', len(a) - 1)
    return 'n' if c else 'y'

def trunc(R, sp, L, k, e):
    keep, ex = L[:R], L[R:]
    k2 = k
    for c in reversed(ex):
        k2 = push(sp, c, k2)
    e2 = e if (not ex or (k == 'b' and all(c == 0 for c in ex))) else 'y'
    return keep, k2, e2

def dec_eff(d): return 'd' if d else 'l'

def step_head(M, R, spL, spR, v, c, r1, kr1, eR):
    q, l, r, kl, kr = v
    tr = M.get((q, c))
    if tr is None: return None
    x, d, q2 = tr
    if d == 'R':
        l2, kl2, eL = trunc(R, spL, (x,) + l, kl, 'l')
        return [(eL, eR, (q2, l2, r1, kl2, kr1))]
    if l:
        r2, kr2, eR2 = trunc(R, spR, (l[0], x) + r1, kr1, eR)
        return [('l', eR2, (q2, l[1:], r2, kl, kr2))]
    out = []
    for c2, k2, dd in pop(spL, kl):
        r2, kr2, eR2 = trunc(R, spR, (c2, x) + r1, kr1, eR)
        out.append((dec_eff(dd), eR2, (q2, (), r2, k2, kr2)))
    return out

def asucc(M, R, spL, spR, v):
    q, l, r, kl, kr = v
    if r:
        return step_head(M, R, spL, spR, v, r[0], r[1:], kr, 'l')
    out = []
    for c, k2, dd in pop(spR, kr):
        x = step_head(M, R, spL, spR, v, c, (), k2, dec_eff(dd))
        if x is None: return None
        out += x
    return out

def start_node(M, t0):
    x = wrun(M, BLANK, BLANK, t0, WINIT)
    if x is None: return None, None
    wc, ls0 = x
    return (wc[0], tuple(int(b) for b in wc[1]), tuple(int(b) for b in wc[2]), 'b', 'b'), ls0

def graph(M, R, spL, spR, start, cap):
    idx = {start: 0}; nodes = [start]; succ = []; effs = []
    i = 0
    while i < len(nodes):
        es = asucc(M, R, spL, spR, nodes[i])
        if es is None: return None
        s = []
        for eL, eR, v in es:
            if v not in idx:
                if len(nodes) >= cap: return None
                idx[v] = len(nodes); nodes.append(v)
            s.append(idx[v])
        succ.append(s); effs.append([(eL, eR) for eL, eR, _ in es])
        i += 1
    return nodes, succ, effs

def tarjan(N, adj):
    sys.setrecursionlimit(1000000)
    index = {}; low = {}; st = []; on = [False] * N; comp = [-1] * N; nc = [0]; cnt = [0]
    def strong(v):
        index[v] = low[v] = cnt[0]; cnt[0] += 1; st.append(v); on[v] = True
        for w in adj[v]:
            if w not in index: strong(w); low[v] = min(low[v], low[w])
            elif on[w]: low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            while True:
                w = st.pop(); on[w] = False; comp[w] = nc[0]
                if w == v: break
            nc[0] += 1
    for v in range(N):
        if v not in index: strong(v)
    return comp  # edges go from higher to lower-or-equal component numbers

def ranks_for(nodes, succ, effs, q):
    """lex ranks (lists of ('c', k) | 'mL' | 'mR'), or None"""
    N = len(nodes)
    alive = [nodes[i][0] != q for i in range(N)]
    E = [(i, j, e) for i in range(N) if alive[i] for j, e in zip(succ[i], effs[i]) if alive[j]]
    comps = []  # per round: (component numbers, measure per component)
    for _ in range(40):
        adj = [[] for _ in range(N)]
        for i, j, e in E: adj[i].append(j)
        comp = tarjan(N, adj)
        inner = [(i, j, e) for i, j, e in E if comp[i] == comp[j]]
        if not inner:
            comps.append((comp, None)); break
        bycomp = {}
        for i, j, e in inner: bycomp.setdefault(comp[i], []).append(e)
        meas = {}
        for cpt, es in bycomp.items():
            ok = None
            for side, k in (('mR', 1), ('mL', 0)):
                if all(e[k] != 'y' for e in es) and any(e[k] == 'd' for e in es):
                    ok = side; break
            if ok is None: return None
            meas[cpt] = ok
        comps.append((comp, meas))
        k_of = {'mL': 0, 'mR': 1}
        E = [(i, j, e) for i, j, e in inner if e[k_of[meas[comp[i]]]] == 'l']
    else:
        return None
    rk = []
    for i in range(N):
        r = []
        for comp, meas in comps:
            r.append(('c', comp[i]))
            if meas is not None:
                r.append(meas.get(comp[i], ('c', 0)))
        rk.append(r)
    return rk

def lexdec(a, b, e):
    for x, y in zip(a, b):
        if isinstance(x, tuple) and isinstance(y, tuple):
            if y[1] < x[1]: return True
            if x[1] != y[1]: return False
            continue
        if x != y: return False
        k = 0 if x == 'mL' else 1
        if e[k] == 'd': return True
        if e[k] == 'y': return False
    return False

def try_cert(M, K, R, t0, spL, spR, cap=3000):
    start, ls0 = start_node(M, t0)
    if start is None: return None
    g = graph(M, R, spL, spR, start, cap)
    if g is None: return None
    nodes, succ, effs = g
    ranks = []
    for q in range(3):
        if not any(v[0] == q for v in nodes):
            if all(not (s == q and k + 1 > K) for k, (s, _) in enumerate(ls0)):
                continue
            return None
        rk = ranks_for(nodes, succ, effs, q)
        if rk is None: return None
        # self-check
        for i in range(len(nodes)):
            if nodes[i][0] == q: continue
            for j, e in zip(succ[i], effs[i]):
                if nodes[j][0] != q: assert lexdec(rk[i], rk[j], e), (i, j, e)
        ranks.append((q, rk))
    return dict(t0=t0, R=R, spL=spL, spR=spR, nodes=nodes, succ=succ, ranks=ranks)

def words(n):
    return [tuple(x) for k in range(1, n + 1) for x in itertools.product((0, 1), repeat=k)]
SIDES = [((), ())] + [(a, w) for a in [()] + words(3) for w in [()] + words(3) if a or w]

def find_cert(M, K=55):
    base = ((), ())
    for R in (2, 3):
        for t0 in (0, 1, 4, 16):
            c = try_cert(M, K, R, t0, base, base)
            if c: return c
    for R in (2, 3):
        for t0 in (0, 1, 4, 16):
            for side in SIDES[1:]:
                for spL, spR in ((side, base), (base, side)):
                    c = try_cert(M, K, R, t0, spL, spR)
                    if c: return c
    return None

SIDES2 = [((), ())] + [(a, w) for a in [()] + words(2) for w in [()] + words(2) if a or w]

def find_cert_full(M, K=55):
    """`find_cert`, then both sides refined at once (slower)"""
    c = find_cert(M, K)
    if c: return c
    for R in (1, 2, 3):
        for t0 in (0, 2, 8):
            for spL in SIDES2:
                for spR in SIDES2:
                    c = try_cert(M, K, R, t0, spL, spR)
                    if c: return c
    return None
