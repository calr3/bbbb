#!/usr/bin/env python3
"""Automatic inductive certificates (rounds with discovered lemmas) for TTT holdouts.

1. Rounds: records (side, state) whose times have constant second differences (also every
   2nd / 3rd record); the configuration C(j) at a record is inferred from 4 consecutive records
   (head on a fresh cell facing outward: ahead blank, behind the inferred side).
2. The round C(j) -> C(j + 1) is proved with induct.py.  When the symbolic run gets stuck in
   front of a repeat, a lemma is guessed: its premise is the region around the head (a few
   items on each side, in the run's variable), its conclusion is read off concrete runs of the
   premise for several j (until the head first reads outside the region) and generalized.  The
   lemma is proved by induction (discovering sub-lemmas the same way), and the round is retried.
Everything is checked by induct.py; the guessing only proposes statements.

usage: auto.py HOLDOUTS [OUT]
Output per machine: `cert T0 inf=... fin=T:last,...` (as bouncer_ttt.py) or `fail <reason>`.
"""
import os, sys, gzip, multiprocessing, collections, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import induct                               # noqa: E402
from induct import Stmt, Fail, tn           # noqa: E402
import bouncer_ttt                          # noqa: E402  (patches bouncer for turmites)
import bouncer                              # noqa: E402

NAMES = [0]
MODE = ['direct']   # search order of the candidate lemmas: 'direct' first, then 'size'
MAXIA = int(os.environ.get("AUTO_IA", 4))
MAXIB = int(os.environ.get("AUTO_IB", 3))
MAXLEMMAS = int(os.environ.get("AUTO_BUDGET", 16))


def cells_of(items, j):
    return induct.expand(items, j)


def sim_region(T, q, A, ea, B, eb, maxsteps=200000):
    """concrete run of a premise: ahead cells A, behind cells B (lists), ends 'X' (unknown,
    stop when read) or 'B' (blank).  Returns (state, facing, post ahead cells, end, post
    behind cells, end) with ends 'XA' / 'XB' / 'B', or None."""
    tape = {}
    for i, x in enumerate(A):
        tape[i] = x
    for i, x in enumerate(B):
        tape[-1 - i] = x
    lo, hi = -len(B), len(A) - 1          # region (grows on blank sides)
    h, d, s = 0, 1, q
    for _ in range(maxsteps):
        if h > hi:
            if ea == 'B':
                hi = h; tape[h] = 0
            else:
                break
        if h < lo:
            if eb == 'B':
                lo = h; tape[h] = 0
            else:
                break
        x = tape[h]
        if (s, x) not in T:
            return None
        w, turn, s2 = T[(s, x)]
        tape[h] = w
        if turn:
            d = -d
        h += d; s = s2
    else:
        return None
    # ahead: from h in direction d to the region end; behind: from h - d the other way
    def run_from(p, dd):
        out = []
        while lo <= p <= hi:
            out.append(tape[p]); p += dd
        return out, ('XA' if dd == 1 else 'XB')
    ah, eah = run_from(h, d)
    be, ebe = run_from(h - d, -d)
    if eah == 'XA' and ea == 'B':
        eah = 'B'
    if eah == 'XB' and eb == 'B':
        eah = 'B'
    if ebe == 'XA' and ea == 'B':
        ebe = 'B'
    if ebe == 'XB' and eb == 'B':
        ebe = 'B'
    if eah == 'B':
        ah = induct.trim(ah)
    if ebe == 'B':
        be = induct.trim(be)
    return s, d, ah, eah, be, ebe


def infer_side(strings):
    """bouncer.infer_side without regular expressions (whose backtracking can hang on some
    tapes): the shape of the last sample, matched greedily against each sample"""
    shape = bouncer.rle_shape(strings[-1])
    counts = []
    for s in strings:
        s = list(s); i = 0; cs = []
        for it in shape:
            if it[0] == 'cell':
                if i >= len(s) or s[i] != it[1]:
                    return None
                i += 1
            else:
                w = list(it[1]); k = 0
                while s[i:i + len(w)] == w:
                    i += len(w); k += 1
                cs.append(k)
        if i != len(s):
            return None
        counts.append(cs)
    reps = [it[1] for it in shape if it[0] == 'rep']
    lin = []
    for j in range(len(reps)):
        c = [cs[j] for cs in counts]
        a = c[1] - c[0]
        if a < 0 or any(c[k + 1] - c[k] != a for k in range(len(c) - 1)):
            return None
        lin.append((a, c[0]))
    side = []; j = 0
    for it in shape:
        if it[0] == 'cell':
            side.append(('l', it[1]))
        else:
            a, b = lin[j]; j += 1
            if a == 0:
                side.extend(('l', x) for x in it[1] * b)
            else:
                side.append(('r', it[1], a, b))
    return side


def generalize(samples):
    """items in j for a list of concrete cell lists at j = j0, j0 + 1, ... (None if not
    linear); repeat counts a*j + b with j counted from j0 = 0"""
    if all(x == samples[0] for x in samples):
        return [('l', c) for c in samples[0]]
    return infer_side(samples)


def guess_lemma(T, cfg, k0, name):
    """lemma candidates from a stuck configuration (in the run variable k >= k0)"""
    q, (A, ea), (B, eb) = cfg
    cands = []
    for ia in range(1, min(len(A), MAXIA) + 1):
        for ib in range(0, min(len(B), MAXIB) + 1):
            pA, pB = A[:ia], B[:ib]
            ends_a = ['B'] if (ia == len(A) and ea == 'B') else ['X']
            ends_b = ['B'] if (ib == len(B) and eb == 'B') else ['X']
            if not any(it[0] == 'r' and it[2] > 0 for it in pA + pB):
                continue
            got = set()
            for pea, peb, start in itertools.product(ends_a, ends_b, (k0, k0 + 1, k0 + 2)):
                if (pea, peb) in got:
                    continue
                posts = []
                for j in range(start, start + 5):
                    r = sim_region(T, q, cells_of(pA, j), pea, cells_of(pB, j), peb)
                    if r is None:
                        break
                    posts.append(r)
                if len(posts) < 5:
                    continue
                if len({(p[0], p[3], p[5]) for p in posts}) != 1:
                    continue
                if posts[0][3] != 'XA':
                    continue      # the head must cross the region (exit on the far side)
                ga = generalize([p[2] for p in posts])
                gb = generalize([p[4] for p in posts])
                if ga is None or gb is None:
                    continue
                # premise in the lemma variable: j = k, valid from `start`; the conclusion was
                # inferred with j counted from `start`: shift it
                def shift(items):
                    out = []
                    for it in items:
                        if it[0] == 'r':
                            out.append(('r', it[1], it[2], it[3] - it[2] * start))
                        else:
                            out.append(it)
                    return out
                p0 = posts[0]
                L = Stmt(name, start, (q, (pA, pea), (pB, peb)),
                         (p0[0], (shift(ga), p0[3]), (shift(gb), p0[5])))
                cands.append(L)
                got.add((pea, peb))
    return cands


def prove_with_discovery(T, L, lemmas, depth=0, budget=None):
    """prove L, discovering lemmas when stuck (depth-first, backtracking over the candidate
    lemmas, larger regions first); on success extends `lemmas`"""
    if budget is None:
        budget = [MAXLEMMAS]
    try:
        induct.prove(T, L, lemmas)
        return True
    except Fail as e:
        places = list(getattr(e, 'stuck', []))
        if getattr(e, 'cfg', None) is not None:
            places.append(e.cfg)
        if not places or depth >= 3:
            return False
        k0 = e.k0
    cands = []
    for cfg in places:
        NAMES[0] += 1
        for C in guess_lemma(T, cfg, k0, f'L{NAMES[0]}'):
            size = len(C.pre[1][0]) + len(C.pre[2][0])
            if all(C.pre != D.pre for _, D in cands):
                cands.append((-size, C))
    cands.sort(key=lambda x: x[0])
    if MODE[0] == 'size':
        # larger regions first, each with its own sub-discovery
        for _, C in cands:
            if budget[0] <= 0:
                return False
            budget[0] -= 1
            sub = list(lemmas)
            if not prove_with_discovery(T, C, sub, depth + 1, budget):
                continue
            sub.append(C)
            if prove_with_discovery(T, L, sub, depth, budget):
                lemmas[:] = sub
                return True
        return False
    # phase 1: candidates that prove without sub-lemmas (cheap); phase 2: with sub-lemmas
    direct, rest = [], []
    for _, C in cands:
        try:
            induct.prove(T, C, list(lemmas))
            direct.append(C)
        except Fail:
            rest.append(C)
    for C in direct:
        if budget[0] <= 0:
            return False
        budget[0] -= 1
        sub = list(lemmas) + [C]
        if prove_with_discovery(T, L, sub, depth, budget):
            lemmas[:] = sub
            return True
    for C in rest:
        if budget[0] <= 0:
            return False
        budget[0] -= 1
        sub = list(lemmas)
        if not prove_with_discovery(T, C, sub, depth + 1, budget):
            continue
        sub.append(C)
        if prove_with_discovery(T, L, sub, depth, budget):
            lemmas[:] = sub
            return True
    return False


def rounds(T):
    """record sequences from a short run, then from a longer one (a regular phase may start
    only after a long transient)"""
    out = []
    for N in (60000, 600000):
        r = rounds_n(T, N)
        out.extend(r[:6])
    if not out:
        out = rounds_n(T, 1000000)
    return out


def rounds_n(T, N):
    tape = collections.defaultdict(int); pos, d, q = 0, 1, 0; lo = hi = 0
    events = collections.defaultdict(list)
    for t in range(1, N + 1):
        s = tape[pos]
        if (q, s) not in T:
            return []
        w, turn, q2 = T[(q, s)]
        tape[pos] = w
        if turn:
            d = -d
        pos += d; q = q2
        if pos > hi:
            hi = pos; events[('R', q)].append(t)
        if pos < lo:
            lo = pos; events[('L', q)].append(t)
    cands = []
    for stride in (1, 2, 3):
        for key, ts0 in events.items():
            for off in range(stride):
                ts = ts0[off::stride]
                if len(ts) < 8:
                    continue
                d2 = [ts[k + 2] - 2 * ts[k + 1] + ts[k] for k in range(len(ts) - 6, len(ts) - 2)]
                r = [ts[k + 1] / max(1, ts[k]) for k in range(len(ts) - 4, len(ts) - 1)]
                # quadratic-time rounds (bouncers) or growing rounds of any kind
                if (len(set(d2)) == 1 and d2[0] > 0) or all(x > 1.05 for x in r):
                    cands.append((stride, -len(ts), ts[0], ts))
    cands.sort()
    return [c[3] for c in cands]


def certificate_mode(nm):
    T = induct.turmite(nm)
    tried = 0
    for ts in rounds(T):
        if tried >= 6:
            break
        # early records, and late ones (after a chaotic transient the regular phase starts late)
        for k0 in list(dict.fromkeys([2, 4, 6, len(ts) - 8, len(ts) - 6])):
            if k0 < 0 or k0 + 5 > len(ts):
                continue
            times = ts[k0:k0 + 5]
            cfgs = [induct.concrete(T, t)[0] for t in times]
            if len({c[0] for c in cfgs}) != 1 or any(induct.trim(c[1]) for c in cfgs):
                continue
            far = infer_side([c[2] for c in cfgs])
            if far is None:
                continue
            tried += 1
            q = cfgs[0][0]
            pre = (q, ([], 'B'), (far, 'B'))
            post = (q, ([], 'B'), (bouncer.shift_n(far), 'B'))
            R = Stmt('round', 0, pre, post, kind='round')
            lemmas = []
            if prove_with_discovery(T, R, lemmas):
                return {'machine': nm, 'T0': times[0], 'lemmas': lemmas, 'round': R}
    return None


def fmt_side(side):
    items, end = side
    out = []
    for it in items:
        if it[0] == 'l':
            out.append(str(it[1]))
        else:
            w = ''.join(map(str, it[1]))
            e = f"{it[2]}j" if it[2] else ''
            e += (f"+{it[3]}" if it[3] > 0 else (f"{it[3]}" if it[3] < 0 else '')) if (it[3] or not e) else ''
            out.append(f"({w})^({e})")
    return ' '.join(out) + f" [{end}]"


def fmt_cfg(c):
    return f"{chr(65 + c[0])}  ahead: {fmt_side(c[1])}  behind: {fmt_side(c[2])}"


def describe(c):
    lines = [f"machine {c['machine']}, round configuration C(0) at step {c['T0']}"]
    for L in c['lemmas'] + [c['round']]:
        lines.append(f"{L.kind} {L.name} (j >= {L.j0}):")
        lines.append(f"    {fmt_cfg(L.pre)}")
        lines.append(f"  ->{fmt_cfg(L.post)}")
    return '\n'.join(lines) + '\n'


def certificate(nm):
    """try both search orders for the lemmas"""
    for mode in ('direct', 'size'):
        MODE[0] = mode
        c = certificate_mode(nm)
        if c is not None:
            return c
    return None


class Timeout(BaseException):
    pass


def _alarm(signum, frame):
    raise Timeout()


def work(nm):
    import signal
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(int(os.environ.get('AUTO_TIMEOUT', 60)))
    try:
        c = certificate(nm)
    except Timeout:
        return nm, 'fail timeout'
    except Exception as e:      # a bug in the guessing must not stop the run
        return nm, f'fail error {e!r}'
    finally:
        signal.alarm(0)
    if c is None:
        return nm, 'fail'
    try:
        inf, never, unres = induct.check(c)
    except Fail as e:
        return nm, f'fail check {e}'
    if os.environ.get('AUTO_DUMP'):
        with open(os.path.join(os.environ['AUTO_DUMP'], nm + '.txt'), 'w') as f:
            f.write(describe(c))
    fin = ','.join(f'{k}:{v}' for k, v in sorted(never.items()) if v)
    extra = f' unresolved={",".join(sorted(unres))}' if unres else ''
    return nm, (f"cert {c['T0']} inf={','.join(sorted(inf))} fin={fin}{extra} "
                f"lemmas={len(c['lemmas'])}")


def main():
    src = sys.argv[1]
    op = gzip.open if src.endswith('.gz') else open
    names = [l.split()[0] for l in op(src, 'rt') if l.strip()]
    out = open(sys.argv[2], 'w') if len(sys.argv) > 2 else sys.stdout
    with multiprocessing.Pool() as pool:
        n = ok = 0
        for nm, res in pool.imap_unordered(work, names, chunksize=1):
            n += 1; ok += res.startswith('cert')
            out.write(f'{nm} {res}\n'); out.flush()
    print(f'{ok}/{n} holdouts with an inductive certificate', file=sys.stderr)


if __name__ == '__main__':
    main()
