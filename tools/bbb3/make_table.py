#!/usr/bin/env python3
"""The value of every 3-state 2-symbol machine (13^6 of them: each transition is one of the 12
proper choices or halting, written `---`), from the certified tree.

Value of a machine: the largest last beep over beep states, where a state visited only finitely
often beeps last at the step after its last visit (steps counted from 1, the halting step
included), a state never visited counts 0, and `inf` means every state is visited infinitely
often.  BBB(3) is the largest finite value.

Writes bbb_3.txt.gz at the repository root (`[value] [machine]`, sorted by value, descending) and
the histogram table used in bbb_3.md (bbb_3_hist.md here)."""
import collections, gzip, itertools, os, pickle, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..')); sys.path.insert(0, os.path.join(HERE, '..', 'bbbb3'))
from gen import wrun, WINIT, BLANK
from gen3 import tomach, name, halt_point
from absgraph import start_node
from gen_bbb3 import cert_labs

INF = 10 ** 9

def value_from(last, io):
    """last: state -> last visit index (absent if never visited); io: set of states visited i.o."""
    if io == {0, 1, 2}:
        return INF
    return max([last[q] + 1 for q in last if q not in io] + [0])

def sim_value(M, N=200000):
    import collections as C
    tape = C.defaultdict(int); h = 0; s = 0; last = {}
    for k in range(N):
        last[s] = k
        w, d, q = M[(s, tape[h])]
        tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    io = {q for q, k in last.items() if k > N // 2}
    return value_from({q: k for q, k in last.items() if q not in io}, io)

def main():
    T, _ = pickle.load(open(os.path.join(HERE, '..', 'bbbb3', 'tree3.pkl'), 'rb'))
    acache = pickle.load(open(os.path.join(HERE, 'abs_certs.pkl'), 'rb'))
    leaves = []  # (P, value, proven)
    def go(T, P):
        if T[0] == 'node':
            i = halt_point(P)[1]
            Q = list(P); Q[i] = 0
            leaves.append((Q, T[1] + 1, True))
            for c, k in enumerate(T[2], 1):
                Q = list(P); Q[i] = c; go(k, Q)
            return
        M = tomach(P)
        if T[0] in ('leaf', 'leafO'):
            ls0, ls = cert_labs(M, T[1])
            io = {s for s, _ in ls}
            last = {}
            for k, (s, _) in enumerate(ls0):
                last[s] = k
            leaves.append((P, value_from(last, io), True))
            return
        c = acache.get(name(P))
        if c is not None:
            io = {q for q, _ in c['ranks']}
            _, ls0 = start_node(M, c['t0'])
            last = {}
            for k, (s, _) in enumerate(ls0):
                last[s] = k
            # a state of the start node (or any node) is ranked, so `last` only matters off `io`
            leaves.append((P, value_from(last, io), True))
            return
        Mf = {k: (int(v[0]), v[1], v[2]) for k, v in M.items() if v is not None}
        leaves.append((P, sim_value(Mf), False))
    go(T, [None] * 6)

    def spec(codes):
        def tt(c):
            if c == 0: return '---'
            x = c - 1
            return f"{x // 6}{'R' if (x // 3) % 2 == 0 else 'L'}{'ABC'[x % 3]}"
        return '_'.join(tt(codes[2 * q]) + tt(codes[2 * q + 1]) for q in range(3))

    hist = collections.Counter(); example = {}; unproven = collections.Counter()
    lines = []
    total = 0
    for P, v, proven in leaves:
        free = [i for i, c in enumerate(P) if c is None]
        for choice in itertools.product(range(13), repeat=len(free)):
            Q = list(P)
            for i, c in zip(free, choice):
                Q[i] = c
            s = spec(Q)
            lines.append((v, s))
            hist[v] += 1
            if not proven:
                unproven[v] += 1
            if v not in example or (s.startswith('1RB') and not example[v].startswith('1RB')):
                example[v] = s
            total += 1
    assert total == 13 ** 6, total
    lines.sort(key=lambda x: (-x[0], x[1]))
    root = os.path.join(HERE, '..', '..')
    with gzip.open(os.path.join(root, 'bbb_3.txt.gz'), 'wt') as f:
        for v, s in lines:
            f.write(f"{'inf' if v == INF else v} {s}\n")
    with open(os.path.join(HERE, 'bbb_3_hist.md'), 'w') as f:
        f.write('| Number of steps | Number of machines | Example machine |\n|---:|---:|---|\n')
        for v in sorted(hist, reverse=True):
            vs = '∞' if v == INF else str(v)
            note = f' ({unproven[v]} by simulation only)' if unproven[v] else ''
            f.write(f'| {vs} | {hist[v]}{note} | `{example[v]}` |\n')
    print('machines', total, 'distinct values', len(hist), 'max finite', max(v for v in hist if v != INF))
    print('unproven', dict(unproven))

if __name__ == '__main__':
    main()
