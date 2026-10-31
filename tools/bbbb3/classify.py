#!/usr/bin/env python3
"""BBBB(3): classify the lazily enumerated 3-state machines with certificates in the exact
semantics of `Window.lean` / `Decider.lean` (the helpers of `tools/gen.py`).

Every leaf of the lazy enumeration (transitions defined when first reached, first move right,
halting choices skipped) gets
* a translated-cycler / cycler certificate found from head records (`record_cert`), checked by the
  window run, and then the bound check `crit` (K = 127) or the beep-dependent `critB`;
* or is a holdout.

Usage: classify.py [K]   writes holdouts3.txt and prints a summary.
"""
import collections, itertools, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
from gen import wrun, ret, fit, crit, seqv, BLANK, ANY, WINIT

NS = 3
K = 127


def sim(M, n):
    """concrete run: labels, head positions, and whether an undefined transition is reached"""
    tape = collections.defaultdict(int); h = 0; s = 0; labs = []; heads = []
    for _ in range(n):
        b = tape[h]
        t = M.get((s, b))
        if t is None:
            return labs, heads, (s, b)
        labs.append((s, b)); heads.append(h)
        w, d, q = t
        tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    heads.append(h)
    return labs, heads, None


def try_window(M, t1, p, kl, kr, nl, nr):
    """the certificate (t1, p, window) if it checks"""
    r = wrun(M, BLANK, BLANK, t1, WINIT)
    if r is None:
        return None
    wc, ls0 = r
    l = list(wc[1]) if kl == BLANK else (wc[1] + [False] * nl)[:nl]
    rr = list(wc[2]) if kr == BLANK else (wc[2] + [False] * nr)[:nr]
    if not (fit(kl, l, wc[1]) and fit(kr, rr, wc[2])):
        return None
    x = wrun(M, kl, kr, p, (wc[0], l, rr))
    if x is None:
        return None
    w1, ls = x
    if w1[0] == wc[0] and ret(kl, l, w1[1]) and ret(kr, rr, w1[2]):
        return ('per', t1, p, l, rr, kl, kr, ls0, ls)
    return None


def record_cert(M, labs, heads, maxback=60):
    """translated cyclers from head records, cyclers from repeated states"""
    n = len(labs)
    hi = lo = 0
    rights = collections.defaultdict(list)   # state -> right-record times
    lefts = collections.defaultdict(list)
    for t in range(n):
        h = heads[t]
        s = labs[t][0]
        if h > hi or t == 0:
            hi = max(hi, h)
            for t1 in reversed(rights[s][-maxback:]):
                depth = heads[t1] - min(heads[t1:t + 1])
                c = try_window(M, t1, t - t1, ANY, BLANK, depth + 1, 0)
                if c:
                    return c
            rights[s].append(t)
        if h < lo or t == 0:
            lo = min(lo, h)
            for t1 in reversed(lefts[s][-maxback:]):
                depth = max(heads[t1:t + 1]) - heads[t1]
                c = try_window(M, t1, t - t1, BLANK, ANY, 0, depth + 2)
                if c:
                    return c
            lefts[s].append(t)
    # cyclers: bounded tape, both sides blank
    seen = {}
    tape = collections.defaultdict(int); h = 0; s = 0
    for t in range(min(n, 4000)):
        key = (s, h, tuple(sorted((c, v) for c, v in tape.items() if v)))
        if key in seen:
            c = try_window(M, seen[key], t - seen[key], BLANK, BLANK, 0, 0)
            if c:
                return c
        seen[key] = t
        w, d, q = M[(s, tape[h])]
        tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    return None


def intervals(pre, per, O, upto):
    labs = [seqv(pre, per, k) for k in range(upto)]
    bo = [k for k, l in enumerate(labs) if O(l)]
    return labs, list(zip(bo, bo[1:]))


def critB(pre, per, K, T):
    """for every boop set and beep set: the period has no boop, or an interval ending before K has
    the value of an interval starting in the first period after the preperiod"""
    t0, p = len(pre), len(per)
    letters = [(q, b) for q in range(NS) for b in (0, 1)]
    for om in range(1, 1 << T):
        Oset = {letters[i] for i in range(T) if om >> i & 1}
        labs, ints = intervals(pre, per, lambda l: (l[0], int(l[1])) in Oset, t0 + 3 * p + 2)
        if not any(t0 <= a < t0 + p for a, _ in ints):
            continue
        early = [(a, b) for a, b in ints if b < K]
        perint = [(a, b) for a, b in ints if t0 <= a < t0 + p]
        for bm in range(1 << T):
            Bset = {letters[i] for i in range(T) if bm >> i & 1}
            val = lambda a, b: sum(1 for k in range(a + 1, b) if (labs[k][0], int(labs[k][1])) in Bset)
            pv = {val(a, b) for a, b in perint}
            if not any(val(a, b) in pv for a, b in early):
                return False
    return True


def name(M):
    def tt(x):
        if x is None:
            return '---'
        w, d, q = x
        return f"{int(w)}{d}{'ABC'[q]}"
    return '_'.join(''.join(tt(M.get((q, b))) for b in (0, 1)) for q in range(NS))


def leaves():
    """lazy enumeration of the non-halting runs (first move right)"""
    stack = [({}, 1, True)]
    while stack:
        M, nused, first = stack.pop()
        labs, heads, und = sim(M, 3000)
        if und is None:
            yield M
            continue
        s, b = und
        for w in (False, True):
            for d in ('R', 'L'):
                if first and d == 'L':
                    continue
                for q in range(min(nused + 1, NS)):
                    M2 = dict(M); M2[(s, b)] = (w, d, q)
                    stack.append((M2, max(nused, q + 1), False))


def main():
    global K
    if len(sys.argv) > 1:
        K = int(sys.argv[1])
    stats = collections.Counter(); holds = []; needB = []
    for M in leaves():
        labs, heads, _ = sim(M, 3000)
        c = record_cert(M, labs, heads)
        if c is None:
            labs, heads, _ = sim(M, 30000)
            c = record_cert(M, labs, heads, maxback=200)
        if c is None:
            holds.append(name(M)); stats['holdout'] += 1
            continue
        ls0, ls = c[7], c[8]
        if crit(ls0, ls, K):
            stats['crit'] += 1
        elif critB(ls0, ls, K, 2 * NS):
            stats['critB'] += 1; needB.append(name(M))
        else:
            stats['FAIL'] += 1; print('FAIL', name(M), 't0', c[1], 'p', c[2], flush=True)
    print(dict(stats))
    print('critB:', needB[:20], len(needB))
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'holdouts3.txt'), 'w') as f:
        f.write(''.join(h + '\n' for h in sorted(holds)))


if __name__ == '__main__':
    main()
