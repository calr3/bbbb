"""Independent simulator for Tooting Terminating Turmites.

usage: python3 sim.py MACHINE TOOT STEPS
Prints the step of each toot (first few and last few), the last toot within STEPS,
and the per-transition last-use times.  Head starts facing right; P = proceed, T = turn
around and move; '---' (or a Z/H target) halts, and the halting step counts as a step.
"""
import sys
from collections import defaultdict

def parse(m):
    rows = m.split('_')
    t = {}
    for q, row in enumerate(rows):
        for s in range(len(row) // 3):
            c = row[3*s:3*s+3]
            if c[0] == '-' or c[2] in 'ZH':
                t[(q, s)] = None
            else:
                t[(q, s)] = (int(c[0]), c[1] == 'T', ord(c[2]) - 65)
    return t

def run(m, toot, steps):
    t = parse(m)
    tq, ts = ord(toot[0]) - 65, int(toot[1])
    tape = defaultdict(int)
    pos, d, q = 0, 1, 0
    toots, last = [], {}
    for step in range(1, steps + 1):
        s = tape[pos]
        last[(q, s)] = step
        if (q, s) == (tq, ts):
            toots.append(step)
        tr = t.get((q, s))
        if tr is None:
            return toots, last, step, True
        w, turn, nq = tr
        tape[pos] = w
        if turn:
            d = -d
        pos += d
        q = nq
    return toots, last, steps, False

if __name__ == '__main__':
    m, toot, steps = sys.argv[1], sys.argv[2], int(sys.argv[3])
    toots, last, n, halted = run(m, toot, steps)
    print(f"{m} toot {toot}: {'halted at step %d' % n if halted else 'ran %d steps' % n}")
    print(f"  toots: {len(toots)}; first {toots[:8]}; last {toots[-3:]}")
    print("  last use:", {f"{chr(65+q)}{s}": v for (q, s), v in sorted(last.items())})
