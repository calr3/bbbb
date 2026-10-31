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

A **tooting** TT also picks one **toot transition**, a pair `(state, symbol)` such as `C1`.  It
is a transition, not a state.  The machine toots every time it executes that transition.  If it
toots finitely often, it **quasihalts** at its last toot.  Its value `t(M)` is the step number
of that last toot, counting steps from 1.  The value is 0 if it never toots.

    TTT(n, m) = max { t(M) : M an n-state m-symbol tooting TT with finitely many toots }

The toot transition may be the halting transition.  A halting machine that toots when it halts
has `t(M)` = its halting time, so **TTT(n, m) ≥ TT(n, m)**.  Halting machines are allowed (a
halting machine toots finitely often).  In every case below the TTT champion does not halt.

## Results

| Domain | TTT value | Champion (toot) | TT for comparison | Status |
|---|---|---|---|---|
| TTT(1, 2) | **= 3** (conjectured) | `1TA---` (A1) | 3 | all machines decided except the bouncer `1TA1PA`, which uses both transitions forever |
| TTT(1, 3) | **= 5** (conjectured) | `1TA2PA---` (A2) | 5 | 6 holdouts, none with a transition that stops being used |
| TTT(1, 4) | **= 9** (conjectured) | `1TA2PA3PA---` (A3) | 9 | 20 holdouts, same |
| TTT(1, 5) | **≥ 13** | `1TA2PA3PA4PA---` (A4) | 13 | 55 holdouts at 10⁵ steps, same |
| TTT(1, 6) | **≥ 19** | `1TA2PA3PA4PA5PA---` (A5) | 19 | 136 holdouts at 10⁵ steps, same |
| TTT(2, 2) | **= 13** (conjectured) | `0TB0PB_1TB1PA` (A1), or the TT champion `1TB---_1PA0PB` (A1) | 13 | 102 holdouts.  Every transition they use stops by step 5 or is still used at step 2·10⁸ |
| TTT(3, 2) | **≥ 90,899** (proven lower bound, conjectured value) | `1TB0PA_0PC1PC_1PA0PB` (C1) | 82 | 17,542 holdouts at 10⁷ steps (see below) |
| TTT(2, 3) | **≥ 3,015,143** (proven lower bound, conjectured value) | `1TB2PB0PB_2TB2PA0PA` (A1) | 223 | 32,697 holdouts at 10⁷ steps (see below) |
| TTT(4, 2) | **≥ 48,186** | TT champion `1TB1PA_1PC0PA_1TA0PD_---1TA` (D0, the halt) | ≥ 48,186 | from TT only; a 20,000-step tree search found nothing it could decide beyond its step limit |
| TTT(2, 4) | **> 3.467·10¹⁵** | TT champion `1TA2PB3TB---_3TA1PB1TA1PA` (A3, the halt) | > 3.467·10¹⁵ | from TT only |

**Proven lower bounds.**  Each champion's value was found by the search, and checked by an
independent simulator (`tools/ttt/sim.py`).  "Proven" means a translated-cycler certificate:
from some step on, the run repeats a fixed period of transitions, shifted along the tape, and
the toot transition is not in that period.

**Upper bounds.**  These are heuristic (a "conjectured" value).  They need every undecided
machine (holdout) to toot infinitely often, or to toot for the last time below the champion's
value.  Simulation suggests this, but it is not proven: there are no bouncer or counter proofs
yet.

### The champions

* **TTT(2, 2) = 13**, `0TB0PB_1TB1PA` toot A1.  It toots twice, at steps 7 and 13.
  From step 16 the machine is a cycler of period 4 using only A0 and B1.  The TT champion
  `1TB---_1PA0PB`, tooting on its halting transition, also scores 13.  So TTT(2) = TT(2) if
  the holdouts behave as simulated.
* **TTT(3, 2) ≥ 90,899**, `1TB0PA_0PC1PC_1PA0PB` toot C1.  It toots 16,081 times; the last
  toot is at step 90,899.  From step 90,913 it is a translated cycler of period 29 that uses
  A0, A1, B0, B1, C0 but never C1.  For comparison, TT(3) ≥ 82 and BBB(3) = 55.
* **TTT(2, 3) ≥ 3,015,143**, `1TB2PB0PB_2TB2PA0PA` toot A1.  It toots 129,411 times; the last
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
TTT(3, 2) and TTT(2, 3) are given as lower bounds.  All other apparent quasihalters among the
3-state holdouts stop tooting by step 452.  Among the 2-state, 3-symbol holdouts they stop by
step 921,268, below the champion.

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
   same tree search) at 10⁷ steps (`ttt N M 10000000 @holdouts.txt`).

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

## Possible next steps

* Bouncer and counter proofs for the holdouts, which would show that the transitions they use
  recur forever (this is what an upper bound needs).  The `bbbb3` bouncer certificates could be
  adapted: a turmite is a 2n-state TM whose states are (state, direction).
* TTT(4, 2) and TTT(2, 4): a full tree search at 20,000 steps (about 2·10⁶ nodes in 2 minutes)
  finds decided values only up to the step limit.  To beat the TT champions it needs much longer
  limits, plus filtering of holdouts (keeping only those with a transition that stops being
  used).
