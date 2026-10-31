#!/usr/bin/env python3
"""BBBB(3): the tree of partial 3-state machines (`Tree.lean`) with certificates, as Lean.

A node is a partial machine (6 entries, `None` = undefined, else a code 1..12 of `decTr 2`); it
runs until it reaches an undefined transition (after `t` steps), and its children are the 12
choices for that transition, in code order.  A leaf (no undefined transition reached in 3000
steps) gets a translated-cycler certificate from `classify.record_cert` passing `crit` with
K = 127, or is a holdout.

Writes lean/Bbbb/Certs3/*.lean and holdouts3_full.txt; prints a summary.
"""
import collections, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..'))
from gen import dec_tr, wrun, wstep, head_r, crit, lean_bools, BLANK, ANY, WINIT
from gen import wrun as _wrun, ret, fit
from classify import sim

K = 127
CUT = 2  # chunks are the subtrees at depth CUT + 1
NS = 3
ROOT = os.path.join(HERE, '..', '..', 'lean', 'Bbbb')


def tomach(P):
    return {(i // 2, i % 2): (None if c is None else dec_tr(2, c)) for i, c in enumerate(P)}


def halt_point(P, limit=3000):
    """(t, idx) when the partial machine halts on an undefined transition, None if not within limit"""
    M = tomach(P)
    w = WINIT
    for t in range(limit):
        b = head_r(BLANK, w[2])
        s = wstep(M, BLANK, BLANK, w)
        if s == 'halt':
            return t, 2 * w[0] + int(b)
        w = s
    return None


def name(P):
    def tt(c):
        if c is None:
            return '---'
        w, d, q = dec_tr(2, c)
        return f"{int(w)}{d}{'ABC'[q]}"
    return '_'.join(tt(P[2 * q]) + tt(P[2 * q + 1]) for q in range(NS))


def canon(P):
    """name up to swapping B, C and mirroring (for caching holdouts)"""
    def tr(P, perm, mir):
        Q = [None] * 6
        for i, c in enumerate(P):
            if c is None:
                continue
            w, d, q = dec_tr(2, c)
            if mir:
                d = 'L' if d == 'R' else 'R'
            q = perm[q]
            x = (6 if w else 0) + (0 if d == 'R' else 3) + q
            Q[2 * perm[i // 2] + i % 2] = x + 1
        return name(Q)
    return min(tr(P, perm, mir) for perm in ((0, 1, 2), (0, 2, 1)) for mir in (False, True))


def tape_at(M, t):
    tape = collections.defaultdict(int); h = 0; s = 0
    for _ in range(t):
        b = tape[h]; w, d, q = M[(s, b)]
        tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    return tape, h, s


def lab_period(labs):
    """minimal (t0, p) with the second half of the labels periodic, else None"""
    n = len(labs); tail = labs[n // 2:]
    for p in range(1, n // 8):
        if tail[p:] == tail[:-p]:
            t0 = n // 2
            while t0 > 0 and labs[t0 - 1] == labs[t0 - 1 + p]:
                t0 -= 1
            return t0, p
    return None


def check_window(M, t1, p, kl, kr, l, r):
    w0 = (tape_at(M, t1)[2], l, r)
    x = _wrun(M, kl, kr, p, w0)
    if x is None:
        return None
    w1, ls = x
    if w1[0] == w0[0] and ret(kl, l, w1[1]) and ret(kr, r, w1[2]):
        return ls
    return None


def fast_cert(M, N):
    """a translated-cycler / cycler certificate (t1, p, l, r, kl, kr, ls0, ls), or None"""
    labs, heads, und = sim(M, N)
    if und is not None:
        return None
    lp = lab_period(labs)
    if lp is None:
        return None
    t0, p0 = lp
    blabs = [(q, bool(b)) for q, b in labs]
    tape, h, s = tape_at(M, t0)
    for t1 in range(t0, min(t0 + 4 * p0 + 1, len(labs) - 4 * p0 - 2)):
        written = [c for c, v in tape.items() if v]
        rblank = all(c < h for c in written)
        lblank = all(c > h for c in written)
        lo = min(written + [h]); hi = max(written + [h])
        for k in (1, 2, 3, 4):
            p = k * p0
            seg = heads[t1:t1 + p + 1]
            opts = []
            if rblank:
                opts.append((ANY, BLANK))
            if lblank:
                opts.append((BLANK, ANY))
            if not opts or (heads[t1 + p] == h):
                opts.append((BLANK, BLANK))
            for kl, kr in opts:
                if kl == ANY:
                    l = [bool(tape[h - 1 - i]) for i in range(h - min(seg) + 1)]
                else:
                    l = [bool(tape[c]) for c in range(h - 1, lo - 1, -1)]
                if kr == ANY:
                    r = [bool(tape[h + i]) for i in range(max(seg) - h + 2)]
                else:
                    r = [bool(tape[c]) for c in range(h, hi + 1)]
                x = _wrun(M, kl, kr, p, (s, l, r))
                if x is None:
                    continue
                w1, ls = x
                if w1[0] == s and ret(kl, l, w1[1]) and ret(kr, r, w1[2]):
                    return (t1, p, l, r, kl, kr, blabs[:t1], ls)
        # one more step
        b = tape[h]; w, d, q = M[(s, b)]
        tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    return None


def crit_o(pre, per, K=K):
    """witnesses for `critO` (Tree.lean), or None"""
    t0, p = len(pre), len(per)
    lab = lambda k: pre[k] if k < t0 else per[(k - t0) % p]
    idx = lambda x: 2 * x[0] + int(x[1])
    N = max(K, t0 + 2 * p) + 1
    labs = [idx(lab(k)) for k in range(N)]
    wit = []
    for om in range(1, 64):
        ob = [bool(om >> i & 1) for i in range(6)]
        bo = [ob[x] for x in labs]
        if not any(bo[t0 + d] for d in range(p)):
            continue
        if sum(1 for k in range(t0, K) if bo[k]) >= 2:
            continue
        boops = [k for k in range(N) if bo[k]]
        ints = list(zip(boops, boops[1:]))
        early = [(i, j) for i, j in ints if j < K]
        perint = [(i, j) for i, j in ints if t0 <= i < t0 + p]
        for bm in range(64):
            bb = [bool(bm >> i & 1) for i in range(6)]
            val = lambda i, j: sum(1 for k in range(i + 1, j) if bb[labs[k]])
            found = None
            for i, j in early:
                for i2, j2 in perint:
                    if val(i, j) == val(i2, j2):
                        found = (i, j, i2, j2); break
                if found:
                    break
            if not found:
                return None
            wit.append((ob, bb) + found)
    return wit


hold_cache = {}
holds = []
stats = collections.Counter()


def leaf(P):
    if (stats['leaf'] + stats['holdout']) % 2000 == 0:
        print('progress', dict(stats), flush=True)
    M = tomach(P)
    key = canon(P)
    if key in hold_cache:
        stats['holdout'] += 1
        holds.append(P)
        return ('hold', len(holds) - 1)
    c = fast_cert(M, 3000) or fast_cert(M, 30000)
    if c is not None and crit(c[6], c[7], K):
        stats['leaf'] += 1
        return ('leaf', c[:6])
    if c is not None:
        wit = crit_o(c[6], c[7])
        if wit is not None:
            stats['leafO'] += 1
            print('leafO:', name(P), 't0', c[0], 'p', c[1], 'witnesses', len(wit), flush=True)
            return ('leafO', c[:6], wit)
        stats['critfail'] += 1
        print('crit fails:', name(P), 't0', c[0], 'p', c[1], flush=True)
    hold_cache[key] = True
    stats['holdout'] += 1
    holds.append(P)
    return ('hold', len(holds) - 1)


def build(P):
    hp = halt_point(P)
    if hp is None:
        return leaf(P)
    t, i = hp
    assert P[i] is None
    kids = []
    for c in range(1, 13):
        Q = list(P); Q[i] = c
        kids.append(build(Q))
    stats['node'] += 1
    return ('node', t, kids)


def lean_tree(T):
    if T[0] == 'leaf':
        t0, p, l, r, kl, kr = T[1]
        return f'.leaf (.per {t0} {p} {lean_bools(l)} {lean_bools(r)} .{kl} .{kr})'
    if T[0] == 'leafO':
        t0, p, l, r, kl, kr = T[1]
        ws = ', '.join(f'({lean_bools(ob)}, {lean_bools(bb)}, {i}, {j}, {i2}, {j2})'
                       for ob, bb, i, j, i2, j2 in T[2])
        return f'.leafO (.per {t0} {p} {lean_bools(l)} {lean_bools(r)} .{kl} .{kr}) [{ws}]'
    if T[0] == 'hold':
        return f'.hold {T[1]}'
    if T[0] == 'chunk':
        return f'.hold {T[1]}'
    return f'.node {T[1]} [' + ', '.join(lean_tree(k) for k in T[2]) + ']'


def lean_pm(P):
    return '[' + ', '.join('none' if c is None else f'some {c}' for c in P) + ']'


def main():
    import pickle
    root = [None] * 6
    cache = os.path.join(HERE, 'tree3.pkl')
    global holds
    if os.path.exists(cache):
        T, holds = pickle.load(open(cache, 'rb'))
    else:
        T = build(root)
        pickle.dump((T, holds), open(cache, 'wb'))
    print(dict(stats), flush=True)
    # chunks: the subtrees at depth 2
    chunks = []
    def cut(T, P, depth):
        if T[0] != 'node':
            return T
        t = T[1]
        i = halt_point(P)[1]
        kids = []
        for c, k in enumerate(T[2], start=1):
            Q = list(P); Q[i] = c
            if depth == CUT and k[0] == 'node':
                chunks.append((Q, k)); kids.append(('chunk', len(chunks) - 1))
            else:
                kids.append(cut(k, Q, depth + 1))
        return ('node', t, kids)
    top = cut(T, root, 0)
    d = os.path.join(ROOT, 'Certs3')
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))
    with open(os.path.join(d, 'Data.lean'), 'w') as f:
        f.write('import Bbbb.Tree\n\n/-! Generated by `tools/bbbb3/gen3.py`: the holdouts and the '
                'chunk roots of the tree of partial 3-state machines. -/\n\nnamespace Bbbb\n\n'
                'set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n')
        f.write('/-- the holdouts (partial machines) -/\ndef holds3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P in holds) + ']\n\n')
        f.write('/-- the roots of the chunks -/\ndef chunkRoots3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P, _ in chunks) + ']\n\nend Bbbb\n')
    for k, (P, C) in enumerate(chunks):
        with open(os.path.join(d, f'C{k}.lean'), 'w') as f:
            f.write('import Bbbb.Certs3.Data\n\nnamespace Bbbb\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n')
            f.write(f'def chunk3_{k} : Tree :=\n  {lean_tree(C)}\n\n')
            f.write(f'theorem chunk3_{k}_ok : checkTree 2 {K} holds3 {lean_pm(P)} chunk3_{k} = true '
                    ':= by decide +kernel\n\nend Bbbb\n')
    with open(os.path.join(d, 'Chunks.lean'), 'w') as f:
        f.write(''.join(f'import Bbbb.Certs3.C{k}\n' for k in range(len(chunks))))
        f.write('\n/-! Generated by `tools/bbbb3/gen3.py`: the top of the tree and the chunks. -/'
                '\n\nnamespace Bbbb\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n')
        f.write(f'/-- the top of the tree, chunks as `.hold` -/\ndef top3 : Tree :=\n  {lean_tree(top)}\n\n')
        f.write(f'theorem top3_ok : checkTree 2 {K} chunkRoots3 [none, none, none, none, none, none] '
                'top3 = true := by decide +kernel\n\n')
        f.write('theorem chunks3_covered (hh : ∀ (k : Nat) (P : PM), holds3[k]? = some P → '
                f'Covered 2 {K} P) :\n    ∀ (k : Nat) (P : PM), chunkRoots3[k]? = some P → '
                f'Covered 2 {K} P := by\n  intro k P h\n  match k with\n')
        for k, (P, C) in enumerate(chunks):
            f.write(f'  | {k} =>\n    have e : some {lean_pm(P)} = some P := '
                    f'(show chunkRoots3[{k}]? = some {lean_pm(P)} from rfl).symm.trans h\n'
                    f'    cases Option.some.inj e; exact checkTree_sound decTr2_surj hh _ _ chunk3_{k}_ok\n')
        f.write(f'  | _ + {len(chunks)} =>\n    exact absurd h (by rw [List.getElem?_eq_none '
                f'(by simp [chunkRoots3])]; simp)\n\nend Bbbb\n')
    with open(os.path.join(HERE, 'holdouts3_full.txt'), 'w') as f:
        f.write(''.join(name(P) + '\n' for P in holds))
    print('chunks', len(chunks), 'holdouts (with symmetric copies)', len(holds),
          'distinct up to symmetry', len({canon(P) for P in holds}))


if __name__ == '__main__':
    main()
