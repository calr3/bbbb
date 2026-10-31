import sys
from collections import defaultdict
from sim import parse
m, steps, every = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
t = parse(m)
tape = defaultdict(int); pos, d, q = 0, 1, 0; lo = hi = 0
for step in range(1, steps+1):
    s = tape[pos]
    w, turn, nq = t[(q, s)]
    tape[pos] = w
    if turn: d = -d
    pos += d; q = nq; lo = min(lo, pos); hi = max(hi, pos)
    if step % every == 0:
        print(step, lo, hi, "zeros:", [i for i in range(lo, hi+1) if tape[i] == 0], "head", pos, "AB C"[q] if False else chr(65+q), d)
