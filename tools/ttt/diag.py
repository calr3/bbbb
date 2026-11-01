"""Diagnose open holdouts: does auto.py find a round with an inferable shape?
Prints per machine: shape (round found and C(j) inferred) or noshape, and the growth class."""
import sys, multiprocessing
import auto, induct, bouncer

def diag(nm):
    T = induct.turmite(nm)
    for ts in auto.rounds(T)[:8]:
        for k0 in sorted({2, 4, 6, len(ts) - 12, len(ts) - 8, len(ts) - 6}):
            if k0 < 0 or k0 + 5 > len(ts):
                continue
            cfgs = [induct.concrete(T, t)[0] for t in ts[k0:k0 + 5]]
            if len({c[0] for c in cfgs}) != 1 or any(induct.trim(c[1]) for c in cfgs):
                continue
            far = bouncer.infer_side([c[2] for c in cfgs])
            if far is not None:
                return nm, 'shape', len(far)
    return nm, 'noshape', 0

if __name__ == '__main__':
    names = [l.split()[-1] for l in open(sys.argv[1])]
    with multiprocessing.Pool() as p:
        for nm, k, n in p.imap_unordered(diag, names):
            print(nm, k, n, flush=True)
