#!/usr/bin/env python3
"""Bouncer certificates for the BBBB(3) holdouts (prototype for a Lean checker).

A *symbolic configuration* C(n) has a state and two tape sides (nearest cell first, blank beyond),
each a list of items: `('l', bit)` a cell, or `('r', w, a, b)` the word `w` (nearest cell first)
repeated `a*n + b` times.  The head reads the first cell of the right side.

A *round* runs C(n) to C(n+1) for every n >= 0 by
* concrete steps (the head cell and, when moving left, the next left cell are cells, not repeats);
* unrolling `('r', w, a, b)` with b >= 1 into the cells of w followed by `('r', w, a, b-1)`;
* shift rules: in state q, with the cells `c` nearest on the left, a run over one copy of `w` on
  the right exits it on the right in state q, never reading beyond c or w, leaving `w2 ++ c` on
  the left with `(w2 ++ c)` starting with `c`; then `w^k` becomes `w2^k` on the left;
* switching to the mirror image (so that blocks on the left are crossed by the same rule).
The transitions of a round are then fixed transitions and words repeated `a*n + b` times.

Usage: bouncer.py [names...]   (default: the bouncer-like holdouts in holdout_types.txt)
"""
import collections, re, sys
sys.path.insert(0, '.'); sys.path.insert(0, '..')
import gen3
from holdout_types import parse


def flip(d):
    return 'L' if d == 'R' else 'R'


def mach(nm):
    M = gen3.tomach(parse(nm))
    return {k: (int(v[0]), v[1], v[2]) for k, v in M.items() if v is not None}


# ---------------------------------------------------------------- concrete simulation

def simulate(M, N, snap=()):
    """labels, heads, and tape snapshots (dict, head, state) at the times in `snap`"""
    tape = collections.defaultdict(int); h = 0; s = 0; labs = []; heads = []; snaps = {}
    snap = set(snap)
    for t in range(N):
        if t in snap:
            snaps[t] = (dict(tape), h, s)
        b = tape[h]; labs.append((s, b)); heads.append(h)
        w, d, q = M[(s, b)]
        tape[h] = w; h += 1 if d == 'R' else -1; s = q
    heads.append(h)
    return labs, heads, snaps


# ---------------------------------------------------------------- symbolic sides

def expand(side, n):
    out = []
    for it in side:
        if it[0] == 'l':
            out.append(it[1])
        else:
            out.extend(list(it[1]) * (it[2] * n + it[3]))
    return out


def strip(side):
    side = list(side)
    while side and ((side[-1][0] == 'l' and side[-1][1] == 0) or
                    (side[-1][0] == 'r' and not any(side[-1][1]))):
        side.pop()
    return side


def rotate_out(side):
    """move cells outward through repeats: x (w' x)^k = (x w')^k x, i.e. a cell before a repeat
    whose word ends with it goes after the repeat, rotating the word"""
    side = list(side)
    changed = True
    while changed:
        changed = False
        for i in range(len(side) - 1):
            it, nx = side[i], side[i + 1]
            if it[0] == 'l' and nx[0] == 'r' and nx[1][-1] == it[1] and (nx[2], nx[3]) != (0, 0):
                w = nx[1]
                side[i] = ('r', (it[1],) + w[:-1], nx[2], nx[3])
                side[i + 1] = it
                changed = True
                break
    return side


def primitive(side):
    """(u^m)^k = u^(m k): the word of a repeat as its primitive root"""
    out = []
    for it in side:
        if it[0] == 'r':
            w = it[1]
            for p in range(1, len(w) + 1):
                if len(w) % p == 0 and w[:p] * (len(w) // p) == w:
                    m = len(w) // p
                    it = ('r', w[:p], it[2] * m, it[3] * m)
                    break
        out.append(it)
    return out


def normalize(side):
    """merge adjacent repeats of the same word and absorb adjacent cell copies of the word"""
    side = rotate_out(primitive(strip(side)))
    changed = True
    while changed:
        changed = False
        out = []
        i = 0
        while i < len(side):
            it = side[i]
            if it[0] == 'r':
                w = it[1]; a, b = it[2], it[3]
                # absorb a copy of w just before (nearer)
                L = len(w)
                if len(out) >= L and all(o[0] == 'l' for o in out[-L:]) and \
                        tuple(o[1] for o in out[-L:]) == w:
                    del out[-L:]; b += 1; changed = True
                # absorb copies just after
                while i + L < len(side) + 1 and i + 1 + L <= len(side) and \
                        all(x[0] == 'l' for x in side[i + 1:i + 1 + L]) and \
                        tuple(x[1] for x in side[i + 1:i + 1 + L]) == w:
                    i += L; b += 1; changed = True
                # merge with the next repeat of the same word
                if i + 1 < len(side) and side[i + 1][0] == 'r' and side[i + 1][1] == w:
                    a += side[i + 1][2]; b += side[i + 1][3]; i += 1; changed = True
                if a == 0 and b == 0:
                    pass
                else:
                    out.append(('r', w, a, b))
            else:
                out.append(it)
            i += 1
        side = strip(out)
        rot = rotate_out(side)
        if rot != side:
            side = rot; changed = True
    return side


# ---------------------------------------------------------------- shape inference

def rle_shape(bits, maxp=12, minrep=3):
    """items for a concrete side: repeats of short words (>= minrep copies), else cells"""
    items = []; i = 0; n = len(bits)
    while i < n:
        best = None
        for p in range(1, maxp + 1):
            w = bits[i:i + p]
            if len(w) < p:
                break
            k = 1
            while bits[i + k * p:i + (k + 1) * p] == w:
                k += 1
            if k >= minrep and (best is None or k * p > best[0] * best[1] or
                                (k * p == best[0] * best[1] and p < best[1])):
                best = (k, p)
        if best:
            k, p = best
            items.append(('rep', tuple(bits[i:i + p]), k)); i += k * p
        else:
            items.append(('cell', bits[i])); i += 1
    return items


def infer_side(strings):
    """a symbolic side whose instances at n = 0, 1, 2, ... are the given concrete sides"""
    shape = rle_shape(strings[-1])
    # regex over '0'/'1' strings
    pat = ''
    reps = []
    for it in shape:
        if it[0] == 'cell':
            pat += str(it[1])
        else:
            pat += '((?:' + ''.join(map(str, it[1])) + ')*)'
            reps.append(it[1])
    rx = re.compile('^' + pat + '$')
    counts = []
    for s in strings:
        m = rx.match(''.join(map(str, s)))
        if not m:
            return None
        counts.append([len(m.group(j + 1)) // len(reps[j]) for j in range(len(reps))])
    # linear counts
    lin = []
    for j in range(len(reps)):
        c = [cs[j] for cs in counts]
        a = c[1] - c[0]
        if any(c[k + 1] - c[k] != a for k in range(len(c) - 1)) or a < 0:
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


# ---------------------------------------------------------------- symbolic round

class Fail(Exception):
    pass


def window_run(M, q, c, w, maxsteps=200):
    """run in state q from the left end of w (cells c to the left), until the head leaves w on
    the right; never reading beyond c or w.  Returns (state, left cells nearest first, labels)"""
    tape = {}
    for i, x in enumerate(w):
        tape[i] = x
    for i, x in enumerate(c):
        tape[-1 - i] = x
    h = 0; s = q; labs = []
    for _ in range(maxsteps):
        if h == len(w):
            left = [tape[-1 - i + len(w)] for i in range(len(w) + len(c))]
            return s, left, labs
        if h < -len(c):
            return None
        b = tape[h]; labs.append((s, b))
        x = M.get((s, b))
        if x is None:
            return None
        wb, d, s2 = x
        tape[h] = wb; h += 1 if d == 'R' else -1; s = s2
    return None


def window_run_look(M, q, c, w, maxsteps=400):
    """run in state q from the left end of w, with one more copy of w after it as lookahead and
    the cells c to the left, until the head is first at the end of the first copy in state q with
    the lookahead copy unchanged and the cells left of it of the form w2 ++ c with (w2 ++ c)
    starting with c.  Never reads beyond c or the lookahead.  Returns (left cells, labels)"""
    n = len(w)
    tape = {i: w[i % n] for i in range(2 * n)}
    for i, x in enumerate(c):
        tape[-1 - i] = x
    h = 0; s = q; labs = []
    for _ in range(maxsteps):
        if h == n and s == q and all(tape[n + i] == w[i] for i in range(n)) and labs:
            left = [tape[n - 1 - i] for i in range(n + len(c))]
            if left[n:] == c and (left[:n] + c)[:len(c)] == c:
                return left, labs, False
            if c and left[:len(c)] == c:
                return left, labs, True
        if h < -len(c) or h >= 2 * n:
            return None
        b = tape[h]; labs.append((s, b))
        x = M.get((s, b))
        if x is None:
            return None
        wb, d, s2 = x
        tape[h] = wb; h += 1 if d == 'R' else -1; s = s2
    return None


def mirror_machine(M):
    return {k: (v[0], flip(v[1]), v[2]) for k, v in M.items()}


def symbolic_round(M, C, stop, maxops=40000):
    """run C (q, L, R) symbolically until `stop(cfg, mirrored)`; returns the final configuration,
    whether it is mirrored, the label items and the operations (the certificate)"""
    q, L, R = C[0], list(C[1]), list(C[2])
    mir = False
    Ms = {False: M, True: mirror_machine(M)}
    labs = []; ops = []
    for _ in range(maxops):
        if ops and stop((q, L, R), mir):
            return (q, L, R), mir, labs, ops
        Mc = Ms[mir]
        if R and R[0][0] == 'r':
            w, a, b = R[0][1], R[0][2], R[0][3]
            done = False
            # copies of w crossed per rule application: j divides the count a*n + b for all n
            for j in (1, 2, 3):
                if a % j:
                    continue
                wj = tuple(w) * j
                aj, bj, rest = a // j, b // j, b % j
                for nc in range(0, 13):
                    if nc > len(L) or any(it[0] != 'l' for it in L[:nc]):
                        break
                    c = [it[1] for it in L[:nc]]
                    res = window_run(Mc, q, c, list(wj))
                    if res is None:
                        continue
                    s2, left, ls = res
                    if s2 != q:
                        continue
                    w2 = left[:len(wj)]
                    if left[len(wj):] == c and (w2 + c)[:nc] == c:
                        L = [('r', tuple(w2), aj, bj)] + L
                    elif nc and left[:nc] == c:
                        # the context travels with the head: c ++ X becomes c ++ w2 ++ X
                        w2 = left[nc:]
                        L = L[:nc] + [('r', tuple(w2), aj, bj)] + L[nc:]
                    else:
                        continue
                    R = [('l', x) for x in w * rest] + R[1:]
                    labs.append(('rep', tuple(ls), aj, bj))
                    ops.append(('shift', j, nc))
                    done = True
                    break
                if done:
                    break
                # with one copy of lookahead: cross all copies but the last
                if bj >= 1 and not done:
                    for nc in range(0, 13):
                        if nc > len(L) or any(it[0] != 'l' for it in L[:nc]):
                            break
                        c = [it[1] for it in L[:nc]]
                        res = window_run_look(Mc, q, c, list(wj))
                        if res is None:
                            continue
                        left, ls, carried = res
                        if (aj, bj - 1) != (0, 0):
                            if carried:
                                L = L[:nc] + [('r', tuple(left[nc:]), aj, bj - 1)] + L[nc:]
                            else:
                                L = [('r', tuple(left[:len(wj)]), aj, bj - 1)] + L
                            labs.append(('rep', tuple(ls), aj, bj - 1))
                        R = [('l', x) for x in wj] + [('l', x) for x in w * rest] + R[1:]
                        ops.append(('shiftlook', j, nc))
                        done = True
                        break
                if done:
                    break
            if done:
                continue
            if b >= 1:
                R = [('l', x) for x in w] + ([('r', w, a, b - 1)] if (a, b - 1) != (0, 0) else []) + R[1:]
                ops.append(('unroll',))
                continue
            e = Fail('cannot cross block')
            e.info = (q, mir, L, R)
            raise e
        # concrete step
        hb = R[0][1] if R else 0
        x = Mc.get((q, hb))
        if x is None:
            raise Fail('undefined transition')
        wb, d, q2 = x
        if d == 'L' and L and L[0][0] == 'r':
            # switch to the mirror image, then the move is to the right
            R0 = R[1:] if R else []
            L, R = R0, [('l', hb)] + L
            mir = not mir
            ops.append(('mirror',))
            continue
        labs.append(('lab', (q, hb)))
        ops.append(('step',))
        Rt = R[1:] if R else []
        if d == 'R':
            L = [('l', wb)] + L; R = Rt
        else:
            c = L[0][1] if L else 0
            L = L[1:]; R = [('l', c), ('l', wb)] + Rt
        q = q2
    raise Fail('too many operations')


def mirror_cfg(C):
    q, L, R = C
    if R and R[0][0] != 'l':
        raise Fail('mirror needs a cell under the head')
    h = R[0] if R else ('l', 0)
    return (q, R[1:] if R else [], [h] + L)


def shift_n(side):
    """the side at n + 1, as a side in n"""
    return [it if it[0] == 'l' else ('r', it[1], it[2], it[2] + it[3]) for it in side]


def same(A, B):
    return A[0] == B[0] and normalize(A[1]) == normalize(B[1]) and normalize(A[2]) == normalize(B[2])


# ---------------------------------------------------------------- driver

def find_rounds(M, N=60000):
    labs, heads, _ = simulate(M, N)
    lo = hi = 0
    events = collections.defaultdict(list)
    for t in range(N):
        h = heads[t]
        if h > hi:
            hi = h; events[('R', labs[t][0])].append(t)
        if h < lo:
            lo = h; events[('L', labs[t][0])].append(t)
    cands = []
    for key, ts in events.items():
        if len(ts) < 8:
            continue
        d2 = [ts[k + 2] - 2 * ts[k + 1] + ts[k] for k in range(len(ts) - 6, len(ts) - 2)]
        if len(set(d2)) == 1 and d2[0] > 0:
            cands.append((len(ts), key, ts))
    cands.sort()
    return cands


last_fail = {}


def Ms_of(M):
    return {False: M, True: mirror_machine(M)}


def certificate(nm, verbose=False):
    M = mach(nm)
    for _, (side, st), ts in find_rounds(M):
        for k0 in (3, 4, 5, 6, 8):
            if k0 + 4 >= len(ts):
                break
            times = ts[k0:k0 + 4]
            _, _, snaps = simulate(M, times[-1] + 1, snap=times)
            sides_far = []
            for t in times:
                tape, h, s = snaps[t]
                cells = [c for c, v in tape.items() if v] + [h]
                lo, hi = min(cells), max(cells)
                if side == 'R':   # head at the right end: the left side matters
                    sides_far.append([tape.get(c, 0) for c in range(h - 1, lo - 1, -1)])
                else:
                    sides_far.append([tape.get(c, 0) for c in range(h + 1, hi + 1)])
            far = infer_side(sides_far)
            if far is None:
                continue
            hb = snaps[times[0]][0].get(snaps[times[0]][1], 0)
            if side == 'R':
                C = (st, far, [('l', hb)])
            else:
                C = (st, [], [('l', hb)] + far)
            target = (st, shift_n(C[1]), shift_n(C[2]))
            tq = target[0]
            tR = len(normalize(target[2]))
            def stop(cfg, mir):
                if cfg[0] != tq:
                    return False
                if mir:
                    try:
                        cfg = mirror_cfg(cfg)
                    except Fail:
                        return False
                return same(cfg, target)
            try:
                final, mir, rlabs, ops = symbolic_round(M, C, stop)
            except Fail as e:
                last_fail[nm] = (e, Ms_of(M))
                if verbose:
                    print('  fail', nm, side, st, k0, e)
                continue
            return {'name': nm, 'T0': times[0], 'C': C, 'mirrored_end': mir, 'labels': rlabs,
                    'ops': ops}
    return None


def work(nm):
    try:
        c = certificate(nm)
    except Exception as e:      # a bug in the prototype must not stop the run
        return nm, None, f'error {e!r}'
    if c is None:
        return nm, None, None
    return nm, c, validate(c)


def main():
    import multiprocessing, pickle
    names = sys.argv[1:] or [l.split()[3] for l in open('holdout_types.txt') if l.startswith('sqrt')]
    with multiprocessing.Pool() as pool:
        results = pool.map(work, names, chunksize=4)
    certs = {}; fails = []; invalid = []
    for nm, c, err in results:
        if c is not None and err is None:
            certs[nm] = c
        elif c is not None:
            invalid.append((nm, err))
        else:
            fails.append(nm if err is None else f'{nm} {err}')
    print(f'{len(certs)}/{len(names)} with a validated bouncer certificate; '
          f'{len(invalid)} invalid: {invalid[:5]}')
    if not sys.argv[1:]:
        pickle.dump(certs, open('bouncer_certs.pkl', 'wb'))
    with open('bouncer_fails.txt', 'w') as f:
        f.write(''.join(x + '\n' for x in fails))




def expand_labels(items, n):
    out = []
    for it in items:
        if it[0] == 'lab':
            out.append(it[1])
        else:
            out.extend(list(it[1]) * (it[2] * n + it[3]))
    return out


def validate(cert, rounds=6):
    """check the certificate against concrete simulation for n = 0 .. rounds-1"""
    M = mach(cert['name'])
    T0 = cert['T0']
    lens = [len(expand_labels(cert['labels'], n)) for n in range(rounds)]
    total = T0 + sum(lens)
    times = [T0 + sum(lens[:n]) for n in range(rounds + 1)]
    labs, heads, snaps = simulate(M, total + 1, snap=times)
    q, Ls, Rs = cert['C']
    for n in range(rounds + 1):
        tape, h, s = snaps[times[n]]
        L = expand(Ls if n == 0 else shift_k(Ls, n), 0)
        R = expand(Rs if n == 0 else shift_k(Rs, n), 0)
        if s != q:
            return f'state at round {n}'
        for i, x in enumerate(L):
            if tape.get(h - 1 - i, 0) != x:
                return f'left side at round {n}'
        for i, x in enumerate(R):
            if tape.get(h + i, 0) != x:
                return f'right side at round {n}'
        cells = [c for c, v in tape.items() if v]
        if any(c < h - len(L) or c >= h + len(R) for c in cells):
            return f'extra cells at round {n}'
        if n < rounds and labs[times[n]:times[n + 1]] != expand_labels(cert['labels'], n):
            return f'labels of round {n}'
    return None


def shift_k(side, k):
    return [it if it[0] == 'l' else ('r', it[1], it[2], it[2] * k + it[3]) for it in side]


if __name__ == '__main__':
    main()
