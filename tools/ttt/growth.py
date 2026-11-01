"""Tape width at steps T and 4T for a list of machines (ratio ~4 linear, ~2 bouncer, ~1 counter)."""
import sys
from collections import defaultdict
from sim import parse
def widths(m, T):
    t = parse(m); tape = defaultdict(int); pos, d, q = 0, 1, 0; lo = hi = 0; out = {}
    for step in range(1, 4*T+1):
        w, turn, nq = t[(q, tape[pos])]
        tape[pos] = w
        if turn: d = -d
        pos += d; q = nq; lo = min(lo, pos); hi = max(hi, pos)
        if step in (T, 4*T): out[step] = hi - lo + 1
    return out[T], out[4*T]
T = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
for l in open(sys.argv[1]):
    m = l.split()[0]
    a, b = widths(m, T)
    print(f"{b/a:.2f} {a} {b} {l.strip()}")
