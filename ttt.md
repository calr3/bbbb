# Tooting Terminating Turmites (TTT)

**Tooting Terminating Turmites** combine two ideas:
* [Terminating Turmites](https://wiki.bbchallenge.org/wiki/Terminating_Turmite) (TT, also
  called relative movement Turing machines). They move relative to their current direction:
  `P` proceeds one cell the same way as the last move, and `T` turns around and moves one cell
  back.
* [Beeping Busy Beavers](https://wiki.bbchallenge.org/wiki/Beeping_Busy_Beaver) (BBB). They
  replace halting with quasihalting.

## Definition

An n-state, m-symbol TT has transitions `(state, symbol) -> (write, P|T, next state)`.  It
starts in state `A`, facing right, on a blank (all-0) tape.  An undefined transition (`---`)
halts.  The halting step counts as a step: it is the `1PZ` of the TT notation, so `1TA---`
here is `1TA1PZ` there.

A **tooting** TT also picks one **toot transition**, a pair `(state, symbol)` such as `C1`. 
The machine toots every time it executes that transition.  If it
toots finitely often, it **quasihalts** at its last toot.  Its value `t(M)` is the step number
of that last toot, counting steps from 1.  The value is 0 if it never toots.

    TTT(n,m) = max { t(M) : M an n-state m-symbol tooting TT with finitely many toots }

The toot transition may be the halting transition.  A halting machine that toots when it halts
has `t(M)` = its halting time, so **TTT(n, m) ≥ TT(n, m)**.  Halting machines are allowed (a
halting machine toots finitely often).  In every case below the TTT champion does not halt.

## Results

| Domain | TTT value | Champion (toot) | TT for comparison | Status |
|---|---|---|---|---|
| TTT(1,2) | **= 3** | `1TA---` (A1) | 3 | proven: the one holdout is certified |
| TTT(1,3) | **= 5** | `1TA2PA---` (A2) | 5 | proven: all 6 holdouts certified |
| TTT(1,4) | **= 9** | `1TA2PA3PA---` (A3) | 9 | proven: all 20 holdouts certified |
| TTT(1,5) | **≥ 13** | `1TA2PA3PA4PA---` (A4) | 13 | 53 of 55 holdouts certified (2 mixed-radix counters open). Probably = 13 |
| TTT(1,6) | **≥ 19** | `1TA2PA3PA4PA5PA---` (A5) | 19 | 126 of 136 holdouts certified. Probably = 19 |
| TTT(2,2) | **= 13** | `0TB0PB_1TB1PA` (A1), or the TT champion `1TB---_1PA0PB` (A1) | 13 | proven: all 102 holdouts certified (85 bouncers, 17 counters / exponential and cubic bouncers) |
| TTT(3,2) | **≥ 90,899** (= 90,899 conjectured) | `1TB0PA_0PC1PC_1PA0PB` (C1) | 82 | 15,618 of 17,542 holdouts certified, none above 59; 1,924 open |
| TTT(2,3) | **≥ 3,015,143** | `1TB2PB0PB_2TB2PA0PA` (A1) | 223 | 26,432 of 32,697 holdouts certified, none above 14,101; 6,265 open. Conjecture: =3,015,143. |
| TTT(4,2) | **≥ 48,186** | TT champion `1TB1PA_1PC0PA_1TA0PD_---1TA` (D0, the halt) | ≥ 48,186 | from TT only; a 20,000-step tree search found nothing it could decide beyond its step limit |
| TTT(2,4) | **> 3.467·10¹⁵** | TT champion `1TA2PB3TB---_3TA1PB1TA1PA` (A3, the halt) | > 3.467·10¹⁵ | from TT only |

"Proven" means: the tree search (`ttt.c`) decides every machine except the holdouts, and every
holdout has a certificate checked by `bouncer_ttt.py` or `induct.py` showing that each of its
transitions is either used forever or used for the last time below the champion's value.  These
checkers are Python programs, not kernel-checked proofs (see *Upper bounds* below).

**Proven lower bounds.**  Each champion's value was found by the search, and checked by an
independent simulator (`tools/ttt/sim.py`).  "Proven" means a translated-cycler certificate:
from some step on, the run repeats a fixed period of transitions, shifted along the tape, and
the toot transition is not in that period.

**Upper bounds.**  See the section *Upper bounds: certificates for the holdouts* below.

### The champions

* **TTT(2,2) = 13**, `0TB0PB_1TB1PA` toot A1.  It toots twice, at steps 7 and 13.
  From step 16 the machine is a cycler of period 4 using only A0 and B1.  The TT champion
  `1TB---_1PA0PB`, tooting on its halting transition, also scores 13, so TTT(2) = TT(2).
* **TTT(3,2) ≥ 90,899**, `1TB0PA_0PC1PC_1PA0PB` toot C1.  It toots 16,081 times; the last
  toot is at step 90,899.  From step 90,913 it is a translated cycler of period 29 that uses
  A0, A1, B0, B1, C0 but never C1.  For comparison, TT(3) ≥ 82 and BBB(3) = 55.
* **TTT(2,3) ≥ 3,015,143**, `1TB2PB0PB_2TB2PA0PA` toot A1.  It toots 129,411 times; the last
  toot is at step 3,015,143.  From step 3,015,163 it is a translated cycler of period 9 using
  A0, A2, B0, B1, B2.  For comparison, TT(2, 3) ≥ 223.

Reproduce:

    python3 tools/ttt/sim.py 1TB0PA_0PC1PC_1PA0PB C1 2000000
    python3 tools/ttt/sim.py 1TB2PB0PB_2TB2PA0PA A1 8000000
    TTT_VERBOSE=1 tools/ttt/ttt 3 2 10000000 1TB0PA_0PC1PC_1PA0PB /dev/null

### Holdouts and false champions (TTT(3, 2))

In a holdout, a transition whose last use is the same at 10⁶ and at 10⁷ steps *looks* like a
quasihalting toot.  For TTT(3, 2) two families of holdouts would beat 90,899 that way.  Both are
chaotic, and both toot again much later:

| Machine (toot) | Apparent last toot (10⁷ steps) | Actual next toot |
|---|---|---|
| `0TB1PB_1PA0PC_1TB1PC` (A0), and 4 closely related variants | 988,058 | 939,182,029 (the variants: by step 2.8·10⁹) |
| `1TB1PC_1PA0PB_1PB1PA` (C1), and 1 variant | 129,903 | 2,416,049,000 |

The first machine leaves a tape of 1s with two or three wandering 0-holes.  It toots (A0) only
when two holes line up next to the head.  That happens more and more rarely as the tape grows
(like √t), but probably infinitely often.  The second machine walls off its right part at step
~130,000 and churns chaotically on the left; it breaks through again at step 2.4·10⁹.  These
are the TTT analogue of BBB's chaotic "probviously infinite" holdouts.  Because of them,
TTT(3,2) and TTT(2,3) are given as lower bounds.  All other apparent quasihalters among the
3-state holdouts stop tooting by step 452.  Among the 2-state, 3-symbol holdouts they stop by
step 921,268, below the champion.

## Visualizer

`tools/ttt/viz/` is a browser tool (Turmite Explorer) that draws space-time diagrams of TTs and
TTTs and reports the last toot, with the same decider as `ttt.c`.  URLs take TT notation,
optionally with a toot transition: `.../explore/1TB0PA_0PC1PC_1PA0PB;C1`.  See its README for
hosting on GitHub Pages.

## Method (`tools/ttt/`)

`ttt.c` enumerates machines in tree normal form.  Undefined transitions are filled in when the
simulation first reaches them, using at most one new state and one new symbol.  Each partial
machine is simulated, and when an undefined transition is reached three things happen:
1. It is a halting leaf: every transition is used finitely often, and a toot on the halting
   transition gives the halting step.
2. The search branches over every definition of that transition.
3. When a run is decided as a **cycler** (exact configuration repeat, by Brent's algorithm) or
   a **translated cycler** (two records on the same side, in the same state, with equal tape
   over the leftward/rightward excursion of the period), the transitions used in one period are
   used forever.  Every other transition is never used again, so its last use is final.  This
   is exact.
4. Otherwise the machine is a holdout.  Holdouts from a 10⁵-step run are run again (with the
   same tree search) at 10⁷ steps (`ttt N M 10000000 @holdouts.txt`), and then with a wider
   translated-cycler window (`ttt_big`, built by `prove.sh`).

`sim.py` is an independent Python simulator.  `longrun.c` runs a single machine for billions of
steps.  `heur.py` lists holdout transitions whose last use is the same at L/10 and L.

Holdout lists are in `tools/ttt/holdouts/`.  Each line is the machine, then `T:a/b` for each
transition T: its last use at L/10 and at L.  The files are `h22_deep`, `h12_deep`,
`h13_deep`, `h14_deep`, `h23_deep.txt.gz` and `h32_deep.txt.gz` (all at L = 10⁷), and `h15`,
`h16` (at L = 10⁵).

    gcc -O2 -o tools/ttt/ttt tools/ttt/ttt.c
    tools/ttt/ttt 3 2 100000 - h32.txt            # tree search, holdouts to h32.txt
    tools/ttt/ttt 3 2 10000000 @h32.txt h32_deep.txt
    python3 tools/ttt/heur.py h32_deep.txt 20

## Upper bounds: certificates for the holdouts

A holdout needs, for each transition `t`, a proof that `t` is used infinitely often, or that it
is never used after some step `T0` (then a toot on `t` scores at most the last use before `T0`,
read from the simulation).  Two certificate checkers do this.

**Bouncer certificates** (`bouncer_ttt.py`).  A turmite is an ordinary 2n-state TM whose states
are (state, facing direction), so the BBBB(3) bouncer prover (`tools/bbbb3/bouncer.py`) applies.
A certificate is a step `T0` and a configuration `C(n)` (tape sides made of cells and words
repeated `a·n + b` times) with a symbolic round from `C(n)` to `C(n+1)` for every `n`.  From
`T0` the run is the sequence of rounds, so the transitions of a round are used forever and all
others never again.  Two additions were needed for turmites: a second normal form for sides
(moving cells inward through repeats, `(x u)^k x = x (u x)^k`, alongside the original outward
rule), and rounds of two or three alternating kinds (every 2nd or 3rd record).

**Inductive certificates** (`induct.py`, found by `auto.py`).  These handle counters,
exponential bouncers (a bouncer with a binary counter inside each round) and cubic bouncers.
Configurations are relative to the head, `(state, ahead, behind)`, which suits turmites: `P`
moves the written cell behind, `T` writes it ahead and swaps the two sides.  A *lemma* says
that for all `j ≥ j0` a local configuration `P(j)` reaches `Q(j)` without reading its unknown
contexts (the conclusion says which context follows each side).  It is proved by induction on
`j`: a base case, and a symbolic run from `P(k+1)` to `Q(k+1)` that may apply the lemma at
`k`.  The symbolic run uses concrete steps, unrolling of repeats that are nonempty for every
`k`, shift rules over fixed words, applications of earlier lemmas (a repeat may be split when
it matches), and identities on sides.  A *round* `C(j) -> C(j+1)` is proved the same way,
without induction, and the configuration at `T0` is checked to be `C(0)`.  Each statement
records the transitions it uses for every `j`, for every large `j`, and possibly.

Example (`0TB0PA_1TA1PB`, a binary counter; `certs/c2x2.py` by hand, `auto.py` finds the
same):

    lemma Z(k):  A at the frame cell, 0^k behind  ->  B carrying past the k digits, now 1^k
      step:  Z(k) on the lower k digits, B0, sweep A1 over 1^k, Z(k) again, B1
    round C(n) -> C(n+1):  Z(n), B1, the new digit B0, sweep A1 over 1^(n+1)

`auto.py` guesses the statements.  It infers `C(j)` from records (head on a fresh cell), and
when the symbolic run is stuck in front of a repeat it cannot cross, it takes the region around
the head as a premise.  It reads the conclusion off concrete runs of the premise for several
`j`, until the head first reads outside the region on the far side, and tries to prove it
(recursively discovering sub-lemmas, with backtracking).  Only the checker matters for
soundness.  The lemma statements found for TTT(2,2) are in `certs/auto22/`.

`prove.sh N M BOUND` runs the whole pipeline.  `results/N_M/` holds the outputs (one line per
holdout: `cert T0 inf=<used forever> fin=<transition:last use>` or `fail`) and `summary.txt`
(from `combine.py`).

| Domain | holdouts (10⁷ steps) | bouncer | translated cycler (wider window) | inductive | open | largest finite last use |
|---|---|---|---|---|---|---|
| (1, 2) | 1 | 1 | | | 0 | 0 |
| (1, 3) | 6 | 5 | | 1 | 0 | 0 |
| (1, 4) | 20 | 15 | | 5 | 0 | 0 |
| (2, 2) | 102 | 85 | | 17 | 0 | 5 |
| (3, 2) | 17,542 | 14,448 | 16 | 1,154 | 1,924 | 59 |
| (2, 3) | 32,697 | 24,068 | 33 | 2,331 | 6,265 | 14,101 |

**What is still open.**  For TTT(3,2) the 1,924 open holdouts are (by tape growth) 900
√t-bouncers, 382 cubic bouncers, 641 counters and 1 linear.  Some are chaotic
(e.g. `0TB1PB_1PA0PC_1TB1PC` above, and machines whose tape looks random), which these methods
cannot handle.  The rest need better lemma guessing (regions spanning several repeats, several
counters, mixed-radix digits).  For TTT(2,3) the 6,265 open holdouts are 3,354
√t-bouncers, 907 cubic bouncers, 1,996 counters and 8 linear (probably translated cyclers with
very long periods).  The open lists are `results/N_M/open.txt`, with growth classes in
`open_growth.txt`.

## Possible next steps

* Better lemma guessing in `auto.py` (the guessed region, conclusions that are not linear in
  `j`, lemmas with two parameters).
* A Lean checker for the inductive certificates, in the style of `lean/Bbbb/Symbolic.lean`.
* A different argument for the chaotic holdouts: they would need a proof that a transition
  recurs, which none of these certificate forms can give.
* TTT(4,2) and TTT(2,4): a full tree search at 20,000 steps (about 2·10⁶ nodes in 2 minutes)
  finds decided values only up to the step limit.  To beat the TT champions it needs much longer
  limits, plus filtering of holdouts (keeping only those with a transition that stops being
  used).
