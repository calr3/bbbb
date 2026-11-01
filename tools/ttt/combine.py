#!/usr/bin/env python3
"""Combine the certificate files of one domain and report what they prove.

usage: combine.py HOLDOUTS CERTFILE... [--bound B]

HOLDOUTS: the holdout list of the tree search (first word of each line = machine).
CERTFILE: outputs of bouncer_ttt.py / auto.py (`name cert T0 inf=.. fin=..`), in any order;
          a machine counts as certified if any file certifies it.  Lines for machines decided
          by a deeper tree search (ttt_big) can be given as `name decided`.
Prints the number of certified holdouts, the largest finite last use among them (a toot on a
transition that is used finitely often), and lists the holdouts still open.
"""
import sys, gzip


def opn(p):
    return gzip.open(p, 'rt') if p.endswith('.gz') else open(p)


def main():
    args = sys.argv[1:]
    bound = None
    if '--bound' in args:
        i = args.index('--bound'); bound = int(args[i + 1]); del args[i:i + 2]
    hold = [l.split()[0] for l in opn(args[0]) if l.strip()]
    best = {}
    for p in args[1:]:
        for l in opn(p):
            w = l.split()
            if len(w) >= 2 and w[1] in ('cert', 'decided'):
                best.setdefault(w[0], l.strip())
    certified = [m for m in hold if m in best]
    open_ = [m for m in hold if m not in best]
    worst = (0, None, None)
    unres = []
    for m in certified:
        w = best[m].split()
        if w[1] != 'cert':
            continue
        for f in w:
            if f.startswith('fin='):
                for kv in filter(None, f[4:].split(',')):
                    k, v = kv.split(':')
                    if int(v) > worst[0]:
                        worst = (int(v), m, k)
            if f.startswith('unresolved='):
                unres.append(m)
    print(f'{len(certified)}/{len(hold)} holdouts certified; largest last use of a transition '
          f'used finitely often: {worst[0]} ({worst[1]} toot {worst[2]})')
    if unres:
        print(f'{len(unres)} certified holdouts have transitions not classified: {unres[:10]}')
    if bound is not None:
        print('all certified holdouts are below the bound' if worst[0] <= bound else
              'a certified holdout BEATS the bound')
    print(f'{len(open_)} open')
    for m in open_[:20]:
        print('  open', m)


if __name__ == '__main__':
    main()
