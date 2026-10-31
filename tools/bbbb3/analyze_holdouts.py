#!/usr/bin/env python3
"""For each distinct BBBB(3) holdout and boop set, which argument bounds g (by simulation):
  factor  - an interval ending before step 127 whose transitions (from its first boop to its last)
            occur again late in the run: g <= its end + 1 for every beep set;
  finite  - no boop late in the run: no g;
  value   - otherwise (beep-set dependent: an early value recurs, or the values grow).
Usage: analyze_holdouts.py [N]   (simulation length, default 200000)"""
import collections, sys
sys.path.insert(0, '.'); sys.path.insert(0, '..')
import gen3
from holdout_types import parse

N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
K = 127
names = [l.split()[3] for l in open('holdout_types.txt')]
kinds = {l.split()[3]: l.split()[0] for l in open('holdout_types.txt')}
stats = collections.Counter(); per_machine = {}
for nm in names:
    M = gen3.tomach(parse(nm))
    tape = collections.defaultdict(int); h = 0; s = 0; labs = bytearray()
    for _ in range(N):
        b = tape[h]; labs.append(2 * s + b)
        w, d, q = M[(s, b)]; tape[h] = int(w); h += 1 if d == 'R' else -1; s = q
    late = bytes(labs[N // 2:])
    res = {}
    for om in range(1, 64):
        bo = [k for k in range(K) if om >> labs[k] & 1]
        found = None
        for i, j in zip(bo, bo[1:]):
            if late.find(bytes(labs[i:j + 1])) >= 0:
                found = j + 1; break
        if found:
            res[om] = ('factor', found)
        elif not any(om >> x & 1 for x in late):
            res[om] = ('finite',)
        else:
            res[om] = ('value',)
        stats[res[om][0]] += 1
    per_machine[nm] = res
    stats['machines_' + kinds[nm]] += 1
    if all(r[0] != 'value' for r in res.values()):
        stats['machines_no_value_' + kinds[nm]] += 1
print(dict(stats))
mx = max(r[1] for res in per_machine.values() for r in res.values() if r[0] == 'factor')
print('max factor bound', mx)
with open('holdout_cases.txt', 'w') as f:
    for nm, res in per_machine.items():
        v = [om for om, r in res.items() if r[0] == 'value']
        f.write(f"{kinds[nm]} {nm} value-boopsets {len(v)} {v[:8]}\n")
