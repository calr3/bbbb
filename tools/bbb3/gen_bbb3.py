#!/usr/bin/env python3
"""BBB(3): certificates for the tree of partial 3-state machines, as Lean (`Bbbb/Bbb/TreeB.lean`).

The tree is the one of `tools/bbbb3/gen3.py` (cached in tools/bbbb3/tree3.pkl): nodes branch on an
undefined transition reached after `t` steps (the halting choice beeps last at step <= t + 1),
leaves are translated cyclers (`checkLeafB`, K = 55) or holdouts.  Holdouts get a recurrence
certificate (`absgraph.find_cert_full`, cached in abs_certs.pkl; without the cache the search
takes about an hour) when one is found; the others stay holdouts.

Writes lean/Bbbb/Bbb/Certs/*.lean and holdouts_bbb3.txt; prints a summary.
"""
import collections, os, sys, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..')); sys.path.insert(0, os.path.join(HERE, '..', 'bbbb3'))
from gen import wrun, WINIT, BLANK, lean_bools
from gen3 import tomach, name, halt_point, lean_pm
from absgraph import find_cert_full

K = 55
CUT = 2
U = 25
ROOT = os.path.join(HERE, '..', '..', 'lean', 'Bbbb', 'Bbb')

def cert_labs(M, c):
    t0, p, l, r, kl, kr = c
    wc, ls0 = wrun(M, BLANK, BLANK, t0, WINIT)
    w1, ls = wrun(M, kl, kr, p, (wc[0], l, r))
    return ls0, ls

def crit_b(ls0, ls):
    for q in range(3):
        if any(s == q for s, _ in ls):
            continue
        if any(s == q and k + 1 > K for k, (s, _) in enumerate(ls0)):
            return False
    return True

def lean_tk(k):
    if k == 'b': return '.blank'
    if k == 'n': return '.nb'
    if k == 'y': return '.any'
    return f'(.{k[0]} {k[1]})'

def lean_comp(x):
    return f'(.c {x[1]})' if isinstance(x, tuple) else '.' + x

def lean_acert(c):
    def sp(s): return f'⟨{lean_bools(map(bool, s[0]))}, {lean_bools(map(bool, s[1]))}⟩'
    nodes = ', '.join(f'(⟨{q}, {lean_bools(map(bool, l))}, {lean_bools(map(bool, r))}, {lean_tk(kl)}, {lean_tk(kr)}⟩, '
                      f'[{", ".join(map(str, s))}])' for (q, l, r, kl, kr), s in zip(c['nodes'], c['succ']))
    ranks = ', '.join(f'({q}, [' + ', '.join('[' + ', '.join(map(lean_comp, a)) + ']' for a in rk) + '])'
                      for q, rk in c['ranks'])
    return (f'{{ t0 := {c["t0"]}, R := {c["R"]}, spL := {sp(c["spL"])}, spR := {sp(c["spR"])}, '
            f'nodes := [{nodes}], ranks := [{ranks}] }}')

def main():
    T, holds_old = pickle.load(open(os.path.join(HERE, '..', 'bbbb3', 'tree3.pkl'), 'rb'))
    cpath = os.path.join(HERE, 'abs_certs.pkl')
    acache = pickle.load(open(cpath, 'rb')) if os.path.exists(cpath) else {}
    stats = collections.Counter()
    holds = []
    def conv(T, P):
        if T[0] == 'node':
            assert T[1] + 1 <= K
            stats['node'] += 1
            i = halt_point(P)[1]
            kids = []
            for c, k in enumerate(T[2], 1):
                Q = list(P); Q[i] = c; kids.append(conv(k, Q))
            return ('node', T[1], kids)
        M = tomach(P)
        if T[0] in ('leaf', 'leafO'):
            ls0, ls = cert_labs(M, T[1])
            assert crit_b(ls0, ls), name(P)
            stats['leaf'] += 1
            return ('leaf', T[1])
        nm = name(P)
        if nm not in acache:
            acache[nm] = find_cert_full(M, K)
        c = acache[nm]
        if c is not None:
            stats['recur'] += 1
            return ('recur', c)
        stats['hold'] += 1
        holds.append(P)
        return ('hold', len(holds) - 1)
    root = [None] * 6
    T = conv(T, root)
    pickle.dump(acache, open(cpath, 'wb'))
    print(dict(stats), flush=True)
    with open(os.path.join(HERE, 'holdouts_bbb3.txt'), 'w') as f:
        f.write(''.join(name(P) + '\n' for P in holds))

    def lean_tree(T):
        if T[0] == 'leaf':
            t0, p, l, r, kl, kr = T[1]
            return f'.leaf (.per {t0} {p} {lean_bools(l)} {lean_bools(r)} .{kl} .{kr})'
        if T[0] == 'recur':
            return f'.recur {lean_acert(T[1])}'
        if T[0] in ('hold', 'ref'):
            return f'.hold {T[1]}'
        return f'.node {T[1]} [' + ', '.join(lean_tree(k) for k in T[2]) + ']'

    wmemo = {}
    def weight(T):
        key = id(T)
        if key not in wmemo:
            if T[0] == 'leaf':
                wmemo[key] = 1 + (T[1][0] + T[1][1]) / 40
            elif T[0] == 'recur':
                wmemo[key] = 2 + len(T[1]['nodes']) / 4
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
    HH = f'(hh : ∀ (j : Nat) (P : PM), holdsB3[j]? = some P → CoveredB 2 {K} P)'

    def lean_forest(F):
        return '[' + ',\n  '.join(f'({lean_pm(P)}, {lean_tree(T)})' for P, T in F) + ']'

    def emit_forests(f, prefix, forests):
        for i, F in enumerate(forests):
            f.write(f'def {prefix}_{i} : List (PM × TreeB 2) :=\n  {lean_forest(F)}\n\n')
            f.write(f'theorem {prefix}_{i}_ok : checkForestB 2 {K} holdsB3 {prefix}_{i} = true := '
                    'by decide +kernel\n\n')
        f.write(f'def {prefix}s : List (List (PM × TreeB 2)) :=\n  [' +
                ', '.join(f'{prefix}_{i}' for i in range(len(forests))) + ']\n\n')
        proof = 'fun _ h => absurd h (List.not_mem_nil _)'
        for i in reversed(range(len(forests))):
            proof = (f'List.forall_mem_cons.2 ⟨checkForestB_sound decTr2_surj hh {prefix}_{i}_ok,\n'
                     f'    {proof}⟩')
        f.write(f'theorem {prefix}s_covered {HH} :\n    ∀ F ∈ {prefix}s, ∀ x ∈ F, CoveredB 2 {K} x.1 :=\n'
                f'  {proof}\n\n')

    d = os.path.join(ROOT, 'Certs')
    os.makedirs(d, exist_ok=True)
    for fn in os.listdir(d):
        os.remove(os.path.join(d, fn))
    with open(os.path.join(d, 'Data.lean'), 'w') as f:
        f.write('import Bbbb.Bbb.TreeB\n\n/-! Generated by `tools/bbb3/gen_bbb3.py`: the BBB(3) holdouts and '
                'the chunk roots of the tree of partial 3-state machines. -/\n\n' + HDR)
        f.write('/-- the holdouts (partial machines) -/\ndef holdsB3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P in holds) + ']\n\n')
        f.write('/-- the roots of the chunks -/\ndef chunkRootsB3 : List PM := [\n  ' +
                ',\n  '.join(lean_pm(P) for P, _ in chunks) + ']\n\nend Bbbb\n')
    nforests = 0
    for k, (P, C) in enumerate(chunks):
        glue, parts = region(C, P)
        forests = pack(parts)
        nforests += len(forests)
        with open(os.path.join(d, f'C{k}.lean'), 'w') as f:
            f.write(f'import Bbbb.Bbb.Certs.Data\n\n/-! Generated by `tools/bbb3/gen_bbb3.py`: chunk {k}. -/\n\n'
                    + HDR)
            emit_forests(f, f'forestB3_{k}', forests)
            f.write(f'theorem glueB3_{k}_ok : checkTreeB 2 {K} (forestB3_{k}s.flatten.map Prod.fst)\n'
                    f'    {lean_pm(P)} ({lean_tree(glue)}) = true := by decide +kernel\n\n')
            f.write(f'theorem chunkB3_{k}_covered {HH} :\n    CoveredB 2 {K} {lean_pm(P)} :=\n'
                    f'  checkTreeB_sound decTr2_surj (coveredB_of_mem (forestsB_covered '
                    f'(Fs := forestB3_{k}s) (forestB3_{k}s_covered hh))) _ _ glueB3_{k}_ok\n\nend Bbbb\n')
    with open(os.path.join(d, 'Chunks.lean'), 'w') as f:
        f.write(''.join(f'import Bbbb.Bbb.Certs.C{k}\n' for k in range(len(chunks))))
        f.write('\n/-! Generated by `tools/bbb3/gen_bbb3.py`: the top of the tree. -/\n\n' + HDR)
        forests = pack(top_items)
        nforests += len(forests)
        emit_forests(f, 'forestTopB3', forests)
        f.write(f'/-- the top of the tree: `.hold j` is a root of the top forests, then a chunk -/\n'
                f'def topB3 : TreeB 2 :=\n  {lean_tree(top_glue)}\n\n')
        f.write(f'theorem topB3_ok : checkTreeB 2 {K} (forestTopB3s.flatten.map Prod.fst ++ chunkRootsB3)\n'
                f'    [none, none, none, none, none, none] topB3 = true := by decide +kernel\n\n')
        proof = 'fun _ h => absurd h (List.not_mem_nil _)'
        for k in reversed(range(len(chunks))):
            proof = f'List.forall_mem_cons.2 ⟨chunkB3_{k}_covered hh,\n    {proof}⟩'
        f.write(f'theorem chunkRootsB3_covered {HH} :\n    ∀ P ∈ chunkRootsB3, CoveredB 2 {K} P :=\n'
                f'  {proof}\n\n')
        f.write(f'/-- every 3-state machine is covered, given the holdouts -/\n'
                f'theorem coverB3 {HH} :\n    CoveredB 2 {K} [none, none, none, none, none, none] :=\n'
                f'  checkTreeB_sound decTr2_surj (coveredB_of_mem (List.forall_mem_append.2\n'
                f'    ⟨forestsB_covered (Fs := forestTopB3s) (forestTopB3s_covered hh), '
                f'chunkRootsB3_covered hh⟩)) _ _ topB3_ok\n\nend Bbbb\n')
    print('chunks', len(chunks), 'forests', nforests, 'holdouts', len(holds))

if __name__ == '__main__':
    main()
