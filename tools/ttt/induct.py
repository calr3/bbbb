#!/usr/bin/env python3
"""Inductive lemmas for Terminating Turmites: a checker for bouncer / counter certificates.

Configurations are relative to the head, which needs no absolute direction:
    (state, ahead, behind)
`ahead` is the tape in the direction the head faces, starting with the cell under the head;
`behind` is the tape on the other side, nearest cell first.  A side is (items, end) where an
item is ('l', s) (a cell) or ('r', word, a, b) (the word, nearest cell first, repeated a*k + b
times; k is the variable of the statement being proved, k >= k0), and end is 'B' (blank
forever) or 'X' (unknown context, which must not be read).

A turmite step on (q, s) -> (w, mv, q'):  P: behind := w : behind, ahead := ahead[1:];
T: ahead := w : ahead[1:], then swap ahead and behind.

A *lemma* L: for every j >= j0, (q, A(j), B(j)) reaches (q', A'(j), B'(j)) without reading the
contexts.  It is proved by induction on j: the base j = j0 by symbolic simulation with all
counts concrete, and the step j = k + 1 for k >= j0 by symbolic simulation from P(k + 1),
which may apply L itself at j = k (or at a constant j0 <= c <= k0... not needed so far) and
any lemma proved before.  A *round* is a lemma with blank ends (no context), C(n) -> C(n+1).
The symbolic simulation uses only:
  * concrete steps (the head cell must be a cell, after unrolling a repeat whose count is >= 1
    for every k >= k0);
  * shift rules: in state q, with the cells c nearest behind, a concrete run over one copy of a
    word w ahead (reading nothing but c and w) leaves w on the far side in state q, with
    behind = w2 ++ c and (w2 ++ c) starting with c, so that w^m becomes w2^m behind (by
    induction over the copies), or with c carried along (behind = c ++ w2);
  * applications of lemmas whose premise matches a prefix of each side (the rest is context);
  * rewriting a side by the identities of bouncer.normalize / normalize_in (both sound).

Each statement records the transitions it certainly uses (for every j >= j0, and for every
large j) and the ones it may use.
"""
import itertools, sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'bbbb3'))
import bouncer                       # noqa: E402  (normal forms of sides)
from bouncer_ttt import normalize_in  # noqa: E402


class Fail(Exception):
    pass


def turmite(nm):
    rows = nm.split('_')
    m = len(rows[0]) // 3
    T = {}
    for q, row in enumerate(rows):
        for s in range(m):
            c = row[3 * s:3 * s + 3]
            if c[0] != '-':
                T[(q, s)] = (int(c[0]), c[1] == 'T', ord(c[2]) - 65)
    return T


def tn(q, s):
    return f"{chr(65 + q)}{s}"


# ------------------------------------------------------------------ counts and sides

def cnt_min(it, k0):
    return it[2] * k0 + it[3]


def expand_const(items):
    """constant repeats (a = 0) as cells"""
    out = []
    for it in items:
        if it[0] == 'r' and it[2] == 0:
            out.extend(('l', x) for x in it[1] * it[3])
        else:
            out.append(it)
    return out


SENT = ('l', 'X')   # stands for an unknown context: stops the stripping of trailing zeros


def norms(items, end='B'):
    """several equivalent forms of a list of items (identities only; trailing zeros are
    dropped only before a blank end)"""
    out = []
    items = expand_const(items)
    for f in (lambda x: list(x), lambda x: bouncer.normalize(list(x)),
              lambda x: normalize_in(list(x))):
        try:
            v = f(list(items) + ([] if end == 'B' else [SENT]))
        except Exception:
            continue
        if end != 'B':
            if not v or v[-1] != SENT:
                continue
            v = v[:-1]
        v = [x for x in v if not (x[0] == 'r' and (x[2], x[3]) == (0, 0))]
        if v not in out:
            out.append(v)
    return out


def strip_blank(items, end):
    if end == 'B':
        return bouncer.strip(items)
    return list(items)


def side_eq(s1, s2):
    (i1, e1), (i2, e2) = s1, s2
    if e1 != e2:
        return False
    i1 = strip_blank(i1, e1); i2 = strip_blank(i2, e2)
    n1, n2 = norms(i1, e1), norms(i2, e2)
    return any(a == b for a in n1 for b in n2)


def subst(items, alpha, beta):
    """items in j, with j = alpha*k + beta, as items in k"""
    out = []
    for it in items:
        if it[0] == 'l':
            out.append(it)
        else:
            a, b = it[2], it[3]
            na, nb = a * alpha, a * beta + b
            if (na, nb) != (0, 0):
                out.append(('r', it[1], na, nb))
    return out


def match_prefix(pat, cur, k0, forced=None, end='X'):
    """match the pattern items (in j) against a prefix of the current items (in k).
    Returns ((alpha, beta) or None, rest) with j = alpha*k + beta.  A repeat matches a repeat
    of the same word.  With j forced, the last pattern item may take only part of a repeat
    (the remainder, nonnegative for every k >= k0, stays in the rest)."""
    sol = forced
    i = 0
    cur = list(cur)
    for pi, p in enumerate(pat):
        if p[0] == 'r' and sol is not None and p[2] * sol[0] == 0 and p[2] * sol[1] + p[3] == 0:
            continue                      # zero copies
        if i >= len(cur):
            if end != 'B':
                return None
            # the blank end supplies zeros
            if p[0] == 'l' and p[1] == 0:
                continue
            if p[0] == 'r' and not any(p[1]) and sol is not None:
                continue
            return None
        c = cur[i]
        if p[0] == 'l':
            if c != p:
                return None
        else:
            if c[0] != 'r' or c[1] != p[1]:
                return None
            pa, pb = p[2], p[3]
            ca, cb = c[2], c[3]
            if sol is not None:
                na, nb = pa * sol[0], pa * sol[1] + pb
                ra, rb = ca - na, cb - nb
                if (ra, rb) != (0, 0):
                    if pi != len(pat) - 1 or ra < 0 or ra * k0 + rb < 0:
                        return None
                    return sol, [('r', c[1], ra, rb)] + cur[i + 1:]
            elif pa == 0:
                if (ca, cb) != (0, pb):
                    return None
            else:
                if ca % pa or (cb - pb) % pa:
                    return None
                sol = (ca // pa, (cb - pb) // pa)
        i += 1
    return sol, cur[i:]


# ------------------------------------------------------------------ statements

class Stmt:
    """premise and conclusion: (q, (A, endA), (B, endB)) with items in the variable j"""
    def __init__(self, name, j0, pre, post, kind='lemma'):
        self.name, self.j0, self.pre, self.post, self.kind = name, j0, pre, post, kind
        self.proved = False
        self.cert = set()      # used for every j >= j0
        self.ecert = set()     # used for every large j
        self.poss = set()      # possibly used


def inst(cfg, alpha, beta):
    q, (A, ea), (B, eb) = cfg
    return (q, (subst(A, alpha, beta), ea), (subst(B, alpha, beta), eb))


class Run:
    """symbolic run of one proof obligation"""
    def __init__(self, T, lemmas, k0, ih=None, maxops=20000):
        self.T, self.lemmas, self.k0, self.ih, self.maxops = T, lemmas, k0, ih, maxops
        self.cert, self.ecert, self.poss = set(), set(), set()
        self.used = []
        self.stuck = []      # configurations facing a repeat that no shift rule crosses

    def label(self, t, always, eventually=True):
        self.poss.add(t)
        if always:
            self.cert.add(t)
        if always or eventually:
            self.ecert.add(t)

    def run(self, cfg, goal):
        q, (A, ea), (B, eb) = cfg
        A, B = list(A), list(B)
        for _ in range(self.maxops):
            cur = (q, (A, ea), (B, eb))
            if os.environ.get('INDUCT_TRACE'):
                print('   ', chr(65 + q), A, ea, '|', B, eb)
            if q == goal[0] and side_eq((A, ea), goal[1]) and side_eq((B, eb), goal[2]):
                return
            # lemma application
            app = self.try_lemmas(cur)
            if app is not None:
                q, (A, ea), (B, eb) = app
                continue
            if A and A[0][0] == 'r':
                sh = self.try_shift(q, A, B)
                if sh is not None:
                    A, B = sh
                    continue
                it = A[0]
                if len(self.stuck) < 3:
                    self.stuck.append((q, (list(A), ea), (list(B), eb)))
                if cnt_min(it, self.k0) >= 1:
                    rest = [] if (it[2], it[3] - 1) == (0, 0) else [('r', it[1], it[2], it[3] - 1)]
                    A = [('l', x) for x in it[1]] + rest + A[1:]
                    continue
                e = Fail(f'cannot cross {it} in state {tn(q, 0)[0]}')
                e.cfg = (q, (A, ea), (B, eb)); e.k0 = self.k0; e.stuck = self.stuck
                raise e
            # concrete step
            if A:
                s = A[0][1]; Arest = A[1:]
            elif ea == 'B':
                s = 0; Arest = []
            else:
                raise Fail('reads the context')
            if (q, s) not in self.T:
                raise Fail(f'undefined transition {tn(q, s)}')
            w, turn, q2 = self.T[(q, s)]
            self.label(tn(q, s), True)
            if turn:
                A, B, ea, eb = B, [('l', w)] + Arest, eb, ea
            else:
                B = [('l', w)] + B; A = Arest
            q = q2
        e = Fail('too many operations')
        e.cfg = None; e.k0 = self.k0; e.stuck = self.stuck
        raise e

    def try_lemmas(self, cur):
        q, (A, ea), (B, eb) = cur
        cands = [(L, False) for L in self.lemmas if L.proved]
        if self.ih is not None:
            cands = [(self.ih, True)] + cands
        for L, is_ih in cands:
            pq, (pA, pea), (pB, peb) = L.pre
            if pq != q:
                continue
            forcings = [(1, 0)] if is_ih else [None, (1, 0), (1, 1), (1, -1), (0, L.j0)]
            for forced, An, Bn in itertools.product(forcings, norms(A, ea), norms(B, eb)):
                    ra = match_prefix(pA, An, self.k0, forced, ea)
                    if ra is None:
                        continue
                    rb = match_prefix(pB, Bn, self.k0, forced if forced else ra[0], eb)
                    if rb is None:
                        continue
                    sa, restA = ra; sb, restB = rb
                    sols = {s for s in (sa, sb) if s is not None}
                    if len(sols) > 1:
                        continue
                    alpha, beta = sols.pop() if sols else (0, L.j0)
                    if alpha < 0 or alpha * self.k0 + beta < L.j0:
                        continue
                    if is_ih and (alpha, beta) != (1, 0):
                        continue       # the induction hypothesis: j = k when proving k + 1
                    # ends: a lemma with context 'X' leaves the rest as it is; 'B' needs a
                    # blank rest
                    if pea == 'B' and (strip_blank(restA, ea) or ea != 'B'):
                        continue
                    if peb == 'B' and (strip_blank(restB, eb) or eb != 'B'):
                        continue
                    oq, (oA, oea), (oB, oeb) = inst(L.post, alpha, beta)
                    ctx = {'XA': (restA, ea), 'XB': (restB, eb)}
                    if pea == 'B':
                        ctx['XA'] = ([], 'B')
                    if peb == 'B':
                        ctx['XB'] = ([], 'B')
                    nblank = (pea == 'B') + (peb == 'B')
                    if (oea, oeb).count('B') > nblank:
                        continue
                    ctx['B'] = ([], 'B')
                    if oea not in ctx or oeb not in ctx or (oea == oeb and oea != 'B'):
                        continue
                    grows = alpha > 0
                    for t in L.poss:
                        self.poss.add(t)
                    for t in L.cert:
                        self.label(t, True)
                    for t in L.ecert:
                        self.label(t, False, grows)
                    self.used.append((L.name, alpha, beta, is_ih))
                    nA, nea = ctx[oea]; nB, neb = ctx[oeb]
                    return (oq, (oA + nA, nea), (oB + nB, neb))
        return None

    def try_shift(self, q, A, B):
        it = A[0]
        w, a, b = it[1], it[2], it[3]
        for j in (1, 2, 3):
            if a % j or b % j:
                continue
            wj = list(w) * j
            for nc in range(0, 9):
                if nc > len(B) or any(x[0] != 'l' for x in B[:nc]):
                    break
                c = [x[1] for x in B[:nc]]
                res = self.window(q, c, wj)
                if res is None:
                    continue
                left, labs = res
                n = len(wj)
                w2 = left[:n]
                if left[n:] == c and (w2 + c)[:nc] == c:
                    newB = [('r', tuple(w2), a // j, b // j)] + B
                elif nc and left[:nc] == c:
                    newB = B[:nc] + [('r', tuple(left[nc:]), a // j, b // j)] + B[nc:]
                else:
                    continue
                always = (a // j) * self.k0 + b // j >= 1
                for t in labs:
                    self.label(t, always, a > 0)
                return A[1:], newB
        return None

    def window(self, q, c, w, maxsteps=400):
        """concrete run from the start of w (facing it), cells c behind; until the head leaves
        w on the far side (in state q).  Returns (cells behind, nearest first; labels)"""
        tape = {i: x for i, x in enumerate(w)}
        for i, x in enumerate(c):
            tape[-1 - i] = x
        h, d, s, labs = 0, 1, q, []
        for _ in range(maxsteps):
            if h == len(w):
                if s != q or not labs:
                    return None
                return [tape[len(w) - 1 - i] for i in range(len(w) + len(c))], labs
            if h < -len(c) or h > len(w):
                return None
            x = tape[h]
            if (s, x) not in self.T:
                return None
            wb, turn, s2 = self.T[(s, x)]
            labs.append(tn(s, x))
            tape[h] = wb
            if turn:
                d = -d
            h += d; s = s2
        return None


def tag(cfg):
    """premise with its contexts named: ahead 'XA', behind 'XB'"""
    q, (A, ea), (B, eb) = cfg
    return (q, (A, 'XA' if ea == 'X' else ea), (B, 'XB' if eb == 'X' else eb))


def goal_of(L, alpha, beta):
    q, (A, ea), (B, eb) = inst(L.post, alpha, beta)
    m = {'XA': 'XA' if L.pre[1][1] == 'X' else L.pre[1][1],
         'XB': 'XB' if L.pre[2][1] == 'X' else L.pre[2][1], 'B': 'B'}
    return (q, (A, m[ea]), (B, m[eb]))


def prove(T, L, lemmas, verbose=False):
    """prove statement L by induction (base j0, step k -> k + 1)"""
    # base
    r0 = Run(T, lemmas, L.j0)
    if L.kind == 'lemma':
        r0.run(tag(inst(L.pre, 0, L.j0)), goal_of(L, 0, L.j0))
    # step: P(k + 1) -> Q(k + 1) for k >= j0, with the induction hypothesis at k
    r1 = Run(T, lemmas, L.j0, ih=L if L.kind == 'lemma' else None)
    if L.kind == 'lemma':
        r1.run(tag(inst(L.pre, 1, 1)), goal_of(L, 1, 1))
    else:                              # a round C(j) -> C(j + 1): directly for every j >= j0
        r1.run(tag(inst(L.pre, 1, 0)), goal_of(L, 1, 0))
    # transitions: every j >= j0 uses the base's (by induction, if the step uses the IH) ...
    uses_ih = any(u[3] for u in r1.used)
    if L.kind == 'lemma' and uses_ih:
        L.cert = set(r0.cert)          # every instance contains an instance at j0
        L.ecert = r0.cert | r1.ecert
    elif L.kind == 'lemma':
        L.cert = r0.cert & r1.cert
        L.ecert = r1.ecert
    else:
        L.cert = set(r1.cert)
        L.ecert = r1.ecert
    L.poss = r0.poss | r1.poss
    L.proved = True
    if verbose:
        print(f'  proved {L.name} (j >= {L.j0}); uses {sorted(set(u[0] for u in r1.used))}; '
              f'certain {sorted(L.cert)}, eventually {sorted(L.ecert)}, possible {sorted(L.poss)}')
    return L


# ------------------------------------------------------------------ certificates

def expand(items, j):
    out = []
    for it in items:
        if it[0] == 'l':
            out.append(it[1])
        else:
            out.extend(list(it[1]) * (it[2] * j + it[3]))
    return out


def concrete(T, steps):
    """configuration after `steps` steps, as (q, ahead cells, behind cells) (blank beyond),
    and the last use of each transition"""
    tape = {}; pos, d, q = 0, 1, 0; last = {}
    for t in range(1, steps + 1):
        s = tape.get(pos, 0)
        last[tn(q, s)] = t
        w, turn, q2 = T[(q, s)]
        tape[pos] = w
        if turn:
            d = -d
        pos += d; q = q2
    cells = [p for p, v in tape.items() if v] + [pos]
    lo, hi = min(cells), max(cells)
    if d == 1:
        ahead = [tape.get(p, 0) for p in range(pos, hi + 1)]
        behind = [tape.get(p, 0) for p in range(pos - 1, lo - 1, -1)]
    else:
        ahead = [tape.get(p, 0) for p in range(pos, lo - 1, -1)]
        behind = [tape.get(p, 0) for p in range(pos + 1, hi + 1)]
    return (q, ahead, behind), last


def trim(c):
    c = list(c)
    while c and c[-1] == 0:
        c.pop()
    return c


def check(cert, verbose=False):
    """cert: {'machine', 'T0', 'lemmas': [Stmt...], 'round': Stmt} with round.pre = C(j),
    round.post = C(j + 1), and the configuration at step T0 equal to C(round.j0).
    Returns (transitions used infinitely often, transitions never used after T0 with their
    last use, unresolved transitions)."""
    T = turmite(cert['machine'])
    proved = []
    for L in cert['lemmas']:
        prove(T, L, proved, verbose); proved.append(L)
    R = cert['round']
    prove(T, R, proved, verbose)
    (q, ah, be), last = concrete(T, cert['T0'])
    cq, (cA, ea), (cB, eb) = R.pre
    assert ea == 'B' and eb == 'B'
    if q != cq or trim(ah) != trim(expand(cA, R.j0)) or trim(be) != trim(expand(cB, R.j0)):
        raise Fail(f'configuration at step {cert["T0"]} is not C({R.j0})')
    alltr = {tn(*k) for k in T}
    inf = set(R.ecert)
    never = {t: last.get(t, 0) for t in alltr - R.poss}
    unresolved = R.poss - R.ecert
    return inf, never, unresolved
