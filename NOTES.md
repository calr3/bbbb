# Notes: towards BBBB(3) and BBBB(2, 3)

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
first move to the right (mirror symmetry).  This includes machines starting `0R…`, which earlier
TNF-only searches missed for BBBB(2).

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
