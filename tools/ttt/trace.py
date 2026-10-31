import sys
from collections import defaultdict
from sim import parse
m, toot, steps = sys.argv[1], sys.argv[2], int(sys.argv[3])
t = parse(m); tq, ts = ord(toot[0])-65, int(toot[1])
tape = defaultdict(int); pos, d, q = 0, 1, 0; lo = hi = 0
for step in range(1, steps+1):
    s = tape[pos]
    if (q, s) == (tq, ts):
        print(step, "toot at pos", pos, "dir", d, "extent", lo, hi)
    w, turn, nq = t[(q, s)]
    tape[pos] = w
    if turn: d = -d
    pos += d; q = nq; lo = min(lo, pos); hi = max(hi, pos)
print("final extent", lo, hi, "pos", pos)
print(''.join(str(tape[i]) for i in range(lo, hi+1))[:400])
