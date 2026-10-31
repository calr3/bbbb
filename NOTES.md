# Notes: towards BBBB(3) and BBBB(2, 3)

## BBBB(3): state of the proof (2026-10-31)

* Lower bound 127 proven (`Champ3.lean`), in all three models.
* Upper bound 127 proven for every machine except those extending one of the 3740 holdout leaves
  of the tree (`Main3.lean`, hypothesis `Holds3Covered`).  Up to mirror image and swapping B/C
  these are 935 machines (`tools/bbbb3/holdout_types.txt`): by tape growth between steps 20000
  and 80000, 774 bouncer-like (width ~ √t) and 161 counter-like (width grows very slowly);
  none grows linearly (every translated cycler found got a certificate).
* Simulation gives `g ≤ 62` for every holdout, so BBBB(3) = 127 is expected.

### Holdouts: what each one needs (`tools/bbbb3/analyze_holdouts.py`)

For each of the 935 holdouts and each of the 63 nonempty boop sets (58905 pairs), simulating
200000 steps:

| case | pairs |
|---|---|
| an interval ending before step 127 whose transitions (first boop to last) recur late: `g` is bounded for every beep set (`factor_interval`); the largest such bound is 62 | 55364 (94%) |
| no boop late in the run: no `g` | 360 |
| depends on the beep set (an early value recurs, or the values grow) | 3181 (5.4%) |

222 holdouts (117 counter-like, 105 bouncer-like) have no beep-set dependent pairs
(`holdout_cases.txt`).  The 935 holdouts have 875 different transition sequences (up to renaming
the transitions), so they need automated provers, not hand proofs.

### Bouncer certificates (`tools/bbbb3/bouncer.py`, prototype for a Lean checker)

A symbolic configuration `C(n)` has tape sides made of cells and words repeated `a·n + b`
times.  A certificate is the start step `T0` (where the configuration is `C(0)`) and a list of
operations taking `C(n)` to `C(n+1)` for every `n`:
* `step`: one concrete step (the head cell, and the next left cell when moving left, are cells);
* `unroll`: a repeat with `b ≥ 1` becomes one copy as cells and the repeat with `b - 1`;
* `shift j nc`: in state `q`, with `nc` cells `c` of context on the left, one checked run over
  `j` copies of the word (no lookahead) leaves the head past them in state `q`, with the left
  side `w2 ++ c` (`(w2 ++ c)` starting with `c`), or with the context carried along
  (`c ++ w2`); by induction over the copies, `w^k` becomes `w2^k`;
* `shiftlook j nc`: the same with one copy of lookahead (needed when crossing a copy peeks at
  the next one, e.g. a hole travelling with the head); it crosses all copies but the last;
* `mirror`: switch to the mirror image, so that blocks on the left are crossed the same way.
The end of the round is compared with `C(n+1)` after normalizing: primitive words
(`(u^m)^k = u^(mk)`), rotation (`x (w x)^k = (x w)^k x`), merging adjacent repeats of a
word and absorbing adjacent copies.  Each rule is an identity to prove once in Lean.

The transitions of a round are then fixed transitions and words repeated `a·n + b` times
(e.g. `1LB1RC_0LC0LA_1RB1LC` from step 23: `C0 (B1 A1 C0)^(n+3) B0 C1^(n+3) C1`).

Status: 743 of the 774 bouncer-like holdouts have a certificate, each checked against
concrete simulation for the first rounds (`validate`).  Not yet covered: 16 without linearly
growing rounds (3 with quadratic rounds, e.g. `1LB0LB_0RC1LB_1LA1RC`, whose round crosses the
block about n times), the rest failing to cross a block or to infer the round's shape.  The
161 counter-like holdouts need a counter prover (generalizing `Holdouts/Counter.lean`); they are
binary counters in various encodings, and exponential bouncers such as
`1LB1RC_1RA1LB_0LB0RA`.

### Next steps

1. Lean checker for bouncer certificates: symbolic sides and their denotation, soundness of each
   operation (`Seg` for all `n`), the normalization identities, then `rounds`.
2. A generic theorem for transitions made of fixed words and words repeated `a·n + b` times
   (generalizing `Holdouts/Bouncer.lean`): near each item boundary the transitions do not
   depend on `n`, so recurring early factors give the 94% case; intervals between boops have
   values `α·n + β`, constant (`g` bounded) or growing (no `g`), for the rest.
3. Counter prover; the remaining bouncers.

## Exploration (2026-10-31)

Exploration only, by simulation (2026-10-31); nothing here is proven yet.  Scripts in
`tools/explore/` (see their docstrings).

## Lower bounds

**BBBB(3) (3 states, 2 symbols) ≥ 127.**  `1RB1LB_0RC0LA_1LC0LA`, boop B1, beep A0 (also B0, C0,
C1, and many larger beep sets).  A translated cycler: values 10, 0, 0, 9, 0, then 5 forever; the
first 5 finishes at step 127.

**BBBB(2, 3) (2 states, 3 symbols) ≥ 187.**  `2RB2LA1RA_1LB1LA0RB`, boop B2, beep B0 (and its
symbol-swapped twin `1RB2RA1LA_2LB0RB2LA`, boop B1).  A holdout: the tape grows slowly to the
right; g = 187 at 20k, 200k and 1M steps, the value 1 recurring throughout (84 times in the last
tenth of the 1M-step run).  The best periodic 2×3 machine gives 134: `1RB2LA0RB_1LA2LB1RA`,
boop B1, beep A1 (values 4, 8, 7, 11, 9, then 9 forever).

## Enumeration

`enumerate.py NS NSYM N` defines a transition only when the run first reaches it (every machine
behaves like one of these leaves; halting choices are skipped since they give no g) and fixes the
first move to the right (mirror symmetry).  This includes machines starting `0R…` (the BBBB(2)
champion is one).

| | non-halting leaves | periodic (by 3000 steps) | holdouts | best periodic g | best holdout g (estimate) |
|---|---|---|---|---|---|
| 2×2 | 130 | 124 | 6 | 18 | 13 |
| 3×2 | 19485 | 18550 | 935 (`holdouts_3x2.txt`) | 127 | ~62 (`1RB1LB_0RC1LB_1LC0LA`, boop B1, beep A0) |
| 2×3 | 19971 | 17745 | 2226 (`holdouts_2x3.txt`) | 134 | 187 |

The holdout lists are "not periodic within 3000 steps with period < 375", so they still contain
some translated cyclers with long preperiods or periods, as well as bouncers, counters, etc.

**Caveat on holdout estimates.**  The naive test "a value repeated ≥ 3 times in the second half
of the run" gives huge false g (≈ N/2) for growing bouncers, whose values each occur a few times
and then increase.  `holdouts.py` counts repeats in the last tenth only and drops estimates above
N/8; `recheck.py` confirms a candidate by checking it is stable as N grows.  A genuine holdout
with g > N/8 would be missed by `holdouts.py` at N = 20000.

## What a proof would need

* **Enumeration:** certify a tree of partial machines instead of all 13⁶ ≈ 4.8M full ones.  New
  soundness lemmas: a machine agreeing with a leaf on the transitions the leaf's run uses has the
  same run (`run_sub`-style), and renaming non-start states preserves g.  `Window.lean` /
  `Decider.lean` carry over; 3-symbol machines need `Bool` generalized to `Fin 3`.
* **Holdouts:** too many for hand proofs as in BBBB(2).  Plan: an automated bouncer decider
  (symbolic rounds with linearly growing repeated blocks, verified by a window-style symbolic run
  with counts) feeding a general version of `Holdouts/Bouncer.lean` for rounds made of fixed
  words and repeated blocks; a generalized counter theorem (`Holdouts/Counter.lean`); the rest
  by hand.  First step: classify the 935 / 2226 holdouts (translated cyclers with long periods,
  bouncers, counters, other).
* **BBBB(3) first:** its champion is a plain translated cycler and its holdouts look small.  For
  BBBB(2, 3) the champion is itself a holdout, so its g = 187 needs a proof of its own.
