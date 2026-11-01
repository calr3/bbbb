"""Print the tape (with head state) at each right/left record or at each visit of a transition."""
import sys
from collections import defaultdict
from sim import parse
m, steps = sys.argv[1], int(sys.argv[2]); ev = sys.argv[3] if len(sys.argv) > 3 else 'rec'
t = parse(m); tape = defaultdict(int); pos, d, q = 0, 1, 0; lo = hi = 0
for step in range(1, steps+1):
    s = tape[pos]
    show = (ev == 'rec' and (pos > hi - 1 or pos < lo + 1) and (pos == hi or pos == lo)) or ev == f"{chr(65+q)}{s}"
    if show:
        print(f"{step:8d} " + ''.join((f"[{chr(65+q)}{'>' if d>0 else '<'}{tape[i]}]" if i == pos else str(tape[i])) for i in range(lo, hi+1)))
    w, turn, nq = t[(q, s)]
    tape[pos] = w
    if turn: d = -d
    pos += d; q = nq; lo = min(lo, pos); hi = max(hi, pos)
