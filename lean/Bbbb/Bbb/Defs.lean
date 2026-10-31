import Bbbb.Defs

/-!
# Beeping Busy Beavers

The definition is the one on the bbchallenge wiki (page "Beeping Busy Beaver", after Shawn
Ligocki).  A machine with `n` states and two symbols starts in state `0` on a blank tape.  Pick a
state `q`; the machine *beeps* at every step taken in state `q` (the transition taken from `q`,
a halting transition included).  If it beeps only finitely often (and at least once), the number
of steps up to and including the last beep is its value for `q`.  `BBB(n)` is the largest such
value over all machines and states.  A halting machine beeps last at its halting step for the
halting state, so `BBB(n) ≥ BB(n)`; a machine quasihalts when some state is visited only
finitely often.

Steps are counted from `1`: the configuration after `k` transitions is in state `q` exactly when
step `k + 1` is taken in `q` (or the machine halts there, taking its halting step in `q`).
-/

namespace Bbbb

open TM

/-- After `k` steps the machine (not yet halted) is in state `q`, so step `k + 1` is taken in
`q`: a beep for the beep state `q`. -/
def InState {n : Nat} (M : Machine (n + 1)) (q : Fin (n + 1)) (k : Nat) : Prop :=
  ∃ c, run M k init = some c ∧ c.q = q

/-- With beep state `q`, the last beep is at step `t` (counted from `1`). -/
def LastBeep {n : Nat} (M : Machine (n + 1)) (q : Fin (n + 1)) (t : Nat) : Prop :=
  ∃ k, InState M q k ∧ t = k + 1 ∧ ∀ k', k < k' → ¬ InState M q k'

/-- `BBB(n + 1) = t`: every last beep of an `(n + 1)`-state machine is at step at most `t`, and
some machine with some beep state beeps last at step `t`. -/
def IsBBB (n t : Nat) : Prop :=
  (∀ (M : Machine (n + 1)) (q : Fin (n + 1)) (s : Nat), LastBeep M q s → s ≤ t) ∧
    ∃ (M : Machine (n + 1)) (q : Fin (n + 1)), LastBeep M q t

end Bbbb
