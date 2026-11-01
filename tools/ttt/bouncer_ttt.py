#!/usr/bin/env python3
"""Bouncer certificates for TTT holdouts, using the BBBB(3) prover (tools/bbbb3/bouncer.py).

A turmite with states A, B, ... is an ordinary TM whose states are (state, facing direction):
TM state 2*q + (0 if facing right else 1).  Transition (q, d) reading s with turmite move P
moves in direction d, with T in the opposite direction, and the new TM state records the new
facing direction.  The start state 0 is (A, facing right).

A certificate (time T0, configuration C(n), a symbolic round from C(n) to C(n+1)) shows that
from T0 the run is the concatenation of the rounds n = 0, 1, 2, ...  So a turmite transition
whose label occurs in the round is used infinitely often, and every other transition has its
last use before T0 (read from concrete simulation).  The round never reads an undefined
transition, so the certificate covers every completion of a partial (holdout) machine.

usage: bouncer_ttt.py HOLDOUTS [OUT]     (HOLDOUTS: lines starting with a machine name)
Writes, per holdout, `cert T0 inf=<transitions> fin=<transition:last use ...>` or `fail`.
"""
import os, sys, gzip, multiprocessing
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'bbbb3'))
import bouncer  # noqa: E402


def turmite(nm):
    rows = nm.split('_')
    m = len(rows[0]) // 3
    T = {}
    for q, row in enumerate(rows):
        for s in range(m):
            c = row[3 * s:3 * s + 3]
            if c[0] == '-':
                continue
            T[(q, s)] = (int(c[0]), c[1] == 'T', ord(c[2]) - 65)
    return T, len(rows), m


def tm_of(nm):
    T, n, m = turmite(nm)
    M = {}
    for (q, s), (w, turn, q2) in T.items():
        for d in (0, 1):                      # 0: facing right, 1: facing left
            nd = 1 - d if turn else d
            M[(2 * q + d, s)] = (w, 'R' if nd == 0 else 'L', 2 * q2 + nd)
    return M


bouncer.mach = tm_of
_round = bouncer.symbolic_round
bouncer.symbolic_round = lambda M, C, stop, maxops=3000: _round(M, C, stop, maxops)


def rotate_in(side):
    """move cells inward (towards the head) through repeats: (x u)^k x = x (u x)^k"""
    side = list(side)
    changed = True
    while changed:
        changed = False
        for i in range(1, len(side)):
            it, pv = side[i], side[i - 1]
            if it[0] == 'l' and pv[0] == 'r' and pv[1][0] == it[1] and (pv[2], pv[3]) != (0, 0):
                w = pv[1]
                side[i - 1] = it
                side[i] = ('r', w[1:] + (it[1],), pv[2], pv[3])
                changed = True
                break
    return side


def absorb(side):
    """merge repeats with adjacent cell copies of their word and with equal neighbours"""
    side = list(side)
    changed = True
    while changed:
        changed = False
        for i, it in enumerate(side):
            if it[0] != 'r':
                continue
            w = it[1]; L = len(w)
            if i >= L and all(x[0] == 'l' for x in side[i - L:i]) and \
                    tuple(x[1] for x in side[i - L:i]) == w:
                side[i - L:i + 1] = [('r', w, it[2], it[3] + 1)]; changed = True; break
            if i + L < len(side) + 0 and all(x[0] == 'l' for x in side[i + 1:i + 1 + L]) and \
                    len(side[i + 1:i + 1 + L]) == L and tuple(x[1] for x in side[i + 1:i + 1 + L]) == w:
                side[i:i + 1 + L] = [('r', w, it[2], it[3] + 1)]; changed = True; break
            if i + 1 < len(side) and side[i + 1][0] == 'r' and side[i + 1][1] == w:
                side[i:i + 2] = [('r', w, it[2] + side[i + 1][2], it[3] + side[i + 1][3])]
                changed = True; break
    return side


def normalize_in(side):
    side = bouncer.primitive(bouncer.strip(side))
    for _ in range(100):
        new = bouncer.strip(absorb(rotate_in(side)))
        new = [x for x in new if not (x[0] == 'r' and (x[2], x[3]) == (0, 0))]
        if new == side:
            break
        side = new
    return side


def same(A, B):
    """equal configurations: equal under either normal form (both use only identities)"""
    if A[0] != B[0]:
        return False
    N = bouncer.normalize
    if N(A[1]) == N(B[1]) and N(A[2]) == N(B[2]):
        return True
    return normalize_in(A[1]) == normalize_in(B[1]) and normalize_in(A[2]) == normalize_in(B[2])


bouncer.same = same


def find_rounds(M, N=60000):
    """records (side, state) whose times have constant second differences, also taking every
    2nd or 3rd record (rounds of two or three alternating kinds)"""
    import collections
    labs, heads, _ = bouncer.simulate(M, N)
    lo = hi = 0
    events = collections.defaultdict(list)
    for t in range(N):
        h = heads[t]
        if h > hi:
            hi = h; events[('R', labs[t][0])].append(t)
        if h < lo:
            lo = h; events[('L', labs[t][0])].append(t)
    cands = []
    for stride in (1, 2, 3):
        for key, ts0 in events.items():
            for off in range(stride):
                ts = ts0[off::stride]
                if len(ts) < 8:
                    continue
                d2 = [ts[k + 2] - 2 * ts[k + 1] + ts[k] for k in range(len(ts) - 6, len(ts) - 2)]
                if len(set(d2)) == 1 and d2[0] > 0:
                    cands.append((stride, -len(ts), key, ts))
    cands.sort()
    return [(-c[1], c[2], c[3]) for c in cands]


bouncer.find_rounds = find_rounds


def tname(s, b):
    return f"{chr(65 + s // 2)}{b}"


def round_transitions(labels):
    out = set()
    for it in labels:
        if it[0] == 'lab':
            out.add(tname(*it[1]))
        else:
            _, ls, a, b = it
            if a > 0 or b > 0:
                out.update(tname(*l) for l in ls)
    return out


def work(nm):
    try:
        c = bouncer.certificate(nm)
    except Exception as e:  # a prover bug must not stop the run
        return nm, f'fail error {e!r}'
    if c is None:
        return nm, 'fail'
    err = bouncer.validate(c)
    if err:
        return nm, f'fail invalid {err}'
    inf = round_transitions(c['labels'])
    # last use before T0 of every other transition
    labs, _, _ = bouncer.simulate(tm_of(nm), c['T0'])
    last = {}
    for t, (s, b) in enumerate(labs):
        last[tname(s, b)] = t + 1             # steps counted from 1
    fin = {k: v for k, v in last.items() if k not in inf}
    return nm, (f"cert {c['T0']} inf={','.join(sorted(inf))} "
                f"fin={','.join(f'{k}:{v}' for k, v in sorted(fin.items()))}")


def main():
    src = sys.argv[1]
    op = gzip.open if src.endswith('.gz') else open
    names = [l.split()[0] for l in op(src, 'rt') if l.strip()]
    out = open(sys.argv[2], 'w') if len(sys.argv) > 2 else sys.stdout
    with multiprocessing.Pool() as pool:
        n = ok = 0
        for nm, res in pool.imap(work, names, chunksize=8):
            n += 1; ok += res.startswith('cert')
            out.write(f'{nm} {res}\n'); out.flush()
    print(f'{ok}/{n} holdouts with a bouncer certificate', file=sys.stderr)


if __name__ == '__main__':
    main()
