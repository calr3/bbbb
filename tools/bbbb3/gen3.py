#!/usr/bin/env python3
"""BBBB(3): the tree of partial 3-state machines (`Tree.lean`) with certificates, as Lean.

A node is a partial machine (6 entries, `None` = undefined, else a code 1..12 of `decTr 2`); it
runs until it reaches an undefined transition (after `t` steps), and its children are the 12
choices for that transition, in code order.  A leaf (no undefined transition reached in 3000
steps) gets a translated-cycler certificate (`fast_cert`) passing `crit` with K = 127, or the
per-boop-set check `critO` with witnesses, or is a holdout.  The tree is cached in tree3.pkl.

Output: the kernel keeps its caches for a whole declaration, so the tree is cut into chunk files
(the subtrees at depth CUT + 1), each a glue tree over forests of weight about U (one
declaration per forest), which keeps every Lean process near 0.5 GB.

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
U = 25   # weight (about the number of leaves) of the subtrees checked in one declaration
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
    if T[0] == 'ref':
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
        def count(T):
            stats[T[0]] += 1
            if T[0] == 'node':
                for k in T[2]:
                    count(k)
        count(T)
    else:
        T = build(root)
        pickle.dump((T, holds), open(cache, 'wb'))
    print(dict(stats), flush=True)
    # regions: the top (nodes down to depth CUT) and the chunks (the subtrees at depth CUT + 1).
    # A region is checked as a glue tree whose `.hold j` refer to the roots of its parts; the
    # parts are checked in forests of weight about U, one declaration each (the kernel keeps its
    # caches for a whole declaration, so small declarations keep the memory of a build small).
    wmemo = {}
    def weight(T):
        key = id(T)
        if key not in wmemo:
            if T[0] == 'leaf':
                wmemo[key] = 1 + (T[1][0] + T[1][1]) / 40
            elif T[0] == 'leafO':
                wmemo[key] = U
            elif T[0] == 'hold':
                wmemo[key] = 0.2
            else:
                wmemo[key] = sum(weight(k) for k in T[2])
        return wmemo[key]

    def pack(items):
        forests, cur, w = [], [], 0
        for P, T in items:
            x = weight(T)
            if cur and w + x > U:
                forests.append(cur); cur, w = [], 0
            cur.append((P, T)); w += x
        if cur:
            forests.append(cur)
        return forests

    def region(T, P):
        parts = []
        def go(T, P):
            if T[0] != 'node' or weight(T) <= U:
                parts.append((P, T))
                return ('ref', len(parts) - 1)
            i = halt_point(P)[1]
            kids = []
            for c, k in enumerate(T[2], start=1):
                Q = list(P); Q[i] = c
                kids.append(go(k, Q))
            return ('node', T[1], kids)
        return go(T, P), parts

    top_items, chunks = [], []
    def top(T, P, depth):
        if T[0] != 'node':
            top_items.append((P, T))
            return ('item', len(top_items) - 1)
        i = halt_point(P)[1]
        kids = []
        for c, k in enumerate(T[2], start=1):
            Q = list(P); Q[i] = c
            if depth == CUT and k[0] == 'node':
                chunks.append((Q, k)); kids.append(('chunk', len(chunks) - 1))
            else:
                kids.append(top(k, Q, depth + 1))
        return ('node', T[1], kids)
    top_glue = top(T, root, 0)
    def fix(G):
        if G[0] == 'item':
            return ('ref', G[1])
        if G[0] == 'chunk':
            return ('ref', len(top_items) + G[1])
        return ('node', G[1], [fix(k) for k in G[2]])
    top_glue = fix(top_glue)

    HDR = 'namespace Bbbb\n\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n'
    HH = '(hh : ∀ (j : Nat) (P : PM), holds3[j]? = some P → Covered 2 127 P)'

    def lean_forest(F):
        return '[' + ',\n  '.join(f'({lean_pm(P)}, {lean_tree(T)})' for P, T in F) + ']'

    def emit_forests(f, prefix, forests):
        for i, F in enumerate(forests):
            f.write(f'def {prefix}_{i} : List (PM × Tree) :=\n  {lean_forest(F)}\n\n')
            f.write(f'theorem {prefix}_{i}_ok : checkForest 2 {K} holds3 {prefix}_{i} = true := '
                    'by decide +kernel\n\n')
        f.write(f'def {prefix}s : List (List (PM × Tree)) :=\n  [' +
                ', '.join(f'{prefix}_{i}' for i in range(len(forests))) + ']\n\n')
        # every forest is covered, as a nested `List.forall_mem_cons`
        proof = 'fun _ h => absurd h (List.not_mem_nil _)'
        for i in reversed(range(len(forests))):
            proof = (f'List.forall_mem_cons.2 ⟨checkForest_sound decTr2_surj hh {prefix}_{i}_ok,\n'
                     f'    {proof}⟩')
        f.write(f'theorem {prefix}s_covered {HH} :\n    ∀ F ∈ {prefix}s, ∀ x ∈ F, Covered 2 {K} x.1 :=\n'
                f'  {proof}\n\n')

    d = os.path.join(ROOT, 'Certs3')
    os.makedirs(d, exist_ok=True)
    for f in os.listdir(d):
        os.remove(os.path.join(d, f))
    with open(os.path.join(d, 'Data.lean'), 'w') as f:
        f.write('import Bbbb.Tree\n\n/-! Generated by `tools/bbbb3/gen3.py`: the holdouts and the '
                'chunk roots of the tree of partial 3-state machines. -/\n\n' + HDR)
        f.write('/-- the holdouts (partial machines) -/\ndef holds3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P in holds) + ']\n\n')
        f.write('/-- the roots of the chunks -/\ndef chunkRoots3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P, _ in chunks) + ']\n\nend Bbbb\n')
    nforests = 0
    for k, (P, C) in enumerate(chunks):
        glue, parts = region(C, P)
        forests = pack(parts)
        nforests += len(forests)
        with open(os.path.join(d, f'C{k}.lean'), 'w') as f:
            f.write(f'import Bbbb.Certs3.Data\n\n/-! Generated by `tools/bbbb3/gen3.py`: chunk {k}. -/\n\n'
                    + HDR)
            emit_forests(f, f'forest3_{k}', forests)
            f.write(f'theorem glue3_{k}_ok : checkTree 2 {K} (forest3_{k}s.flatten.map Prod.fst)\n'
                    f'    {lean_pm(P)} ({lean_tree(glue)}) = true := by decide +kernel\n\n')
            f.write(f'theorem chunk3_{k}_covered {HH} :\n    Covered 2 {K} {lean_pm(P)} :=\n'
                    f'  checkTree_sound decTr2_surj (covered_of_mem (forests_covered '
                    f'(Fs := forest3_{k}s) (forest3_{k}s_covered hh))) _ _ glue3_{k}_ok\n\nend Bbbb\n')
    with open(os.path.join(d, 'Chunks.lean'), 'w') as f:
        f.write(''.join(f'import Bbbb.Certs3.C{k}\n' for k in range(len(chunks))))
        f.write('\n/-! Generated by `tools/bbbb3/gen3.py`: the top of the tree. -/\n\n' + HDR)
        forests = pack(top_items)
        nforests += len(forests)
        emit_forests(f, 'forestTop3', forests)
        f.write(f'/-- the top of the tree: `.hold j` is a root of the top forests, then a chunk -/\n'
                f'def top3 : Tree :=\n  {lean_tree(top_glue)}\n\n')
        f.write(f'theorem top3_ok : checkTree 2 {K} (forestTop3s.flatten.map Prod.fst ++ chunkRoots3)\n'
                f'    [none, none, none, none, none, none] top3 = true := by decide +kernel\n\n')
        proof = 'fun _ h => absurd h (List.not_mem_nil _)'
        for k in reversed(range(len(chunks))):
            proof = f'List.forall_mem_cons.2 ⟨chunk3_{k}_covered hh,\n    {proof}⟩'
        f.write(f'theorem chunkRoots3_covered {HH} :\n    ∀ P ∈ chunkRoots3, Covered 2 {K} P :=\n'
                f'  {proof}\n\n')
        f.write(f'/-- every 3-state machine is covered, given the holdouts -/\n'
                f'theorem cover3 {HH} :\n    Covered 2 {K} [none, none, none, none, none, none] :=\n'
                f'  checkTree_sound decTr2_surj (covered_of_mem (List.forall_mem_append.2\n'
                f'    ⟨forests_covered (Fs := forestTop3s) (forestTop3s_covered hh), '
                f'chunkRoots3_covered hh⟩)) _ _ top3_ok\n\nend Bbbb\n')
    print('forest declarations', nforests)
    with open(os.path.join(HERE, 'holdouts3_full.txt'), 'w') as f:
        f.write(''.join(name(P) + '\n' for P in holds))
    print('chunks', len(chunks), 'top items', len(top_items), 'holdouts (with symmetric copies)', len(holds),
          'distinct up to symmetry', len({canon(P) for P in holds}))


if __name__ == '__main__':
    main()
