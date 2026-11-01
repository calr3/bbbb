"""Summarize certificate files: largest finite last use, and agreement with simulation."""
import sys, gzip, re
cert, hold = sys.argv[1], sys.argv[2]
op = gzip.open if hold.endswith('.gz') else open
sim = {}
for l in op(hold, 'rt'):
    w = l.split()
    sim[w[0]] = {f.split(':')[0]: tuple(map(int, f.split(':')[1].split('/'))) for f in w[1:]}
best = []; bad = 0; n = 0; T0max = 0
for l in open(cert):
    w = l.split()
    if w[1] != 'cert': continue
    n += 1; T0max = max(T0max, int(w[2]))
    inf = set(w[3][4:].split(',')) - {''}
    fin = dict((k, int(v)) for k, v in (x.split(':') for x in w[4][4:].split(',') if x))
    for t, (a, b) in sim[w[0]].items():
        if t in inf and b < 9000000: bad += 1; print('inconsistent inf', w[0], t, a, b)
        if t in fin and fin[t] != b: bad += 1; print('inconsistent fin', w[0], t, fin[t], b)
    for t, v in fin.items(): best.append((v, w[0], t))
best.sort()
print(f'{n} certificates, {bad} inconsistent, largest T0 {T0max}, largest finite last uses:', best[-4:])
