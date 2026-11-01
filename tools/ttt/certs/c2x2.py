"""Hand-written inductive certificates for the TTT(2, 2) holdouts that are not bouncers.
States A = 0, B = 1.  Items: ('l', s) a cell, ('r', word, a, b) the word repeated a*j + b times.
A lemma's premise ends 'X' (unknown context); its conclusion's ends say which context follows:
'XA' the premise's ahead context, 'XB' its behind context."""
from induct import Stmt

def r(w, a, b):
    return ('r', tuple(w), a, b)

def l(s):
    return ('l', s)

A, B = 0, 1
CERTS = []

# 0TB0PA_1TA1PB: a binary counter growing to the left, the head returning to a frame cell.
# Z(k): A at the frame, 0^k behind  ->  B carrying past the k lowest digits, now 1^k.
Z = Stmt('Z', 0, (A, ([l(0)], 'X'), ([r([0], 1, 0)], 'X')),
                 (B, ([], 'XB'), ([r([1], 1, 0), l(0)], 'XA')))
R = Stmt('round', 0, (A, ([l(0)], 'B'), ([r([0], 1, 0), l(1)], 'B')),
                     (A, ([l(0)], 'B'), ([r([0], 1, 1), l(1)], 'B')), kind='round')
CERTS.append({'machine': '0TB0PA_1TA1PB', 'T0': None, 'lemmas': [Z], 'round': R})
