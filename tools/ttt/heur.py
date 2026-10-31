"""Summarize a holdout file: for each holdout, transitions whose last use did not change
between L/10 and L (heuristically used finitely often); print the largest such values."""
import sys
rows = []
for line in open(sys.argv[1]):
    w = line.split()
    if not w: continue
    for f in w[1:]:
        t, v = f.split(':'); a, b = map(int, v.split('/'))
        if a == b and b > 0:
            rows.append((b, w[0], t))
rows.sort(reverse=True)
for r in rows[:int(sys.argv[2]) if len(sys.argv) > 2 else 10]:
    print(*r)
