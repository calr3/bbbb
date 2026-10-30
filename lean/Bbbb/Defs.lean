import Bbbb.Core.Basic

/-!
# Beeping Booping Busy Beavers

The definition is the one on the bbchallenge wiki (page "Beeping Busy Beaver", section on
Bram Cohen's *Beeping Booping Busy Beavers*).

A machine with `n` states and two symbols starts in state `0` on a blank tape.  Some of its
transitions are *beeps*, some are *boops* (a transition is a pair state × symbol read; it beeps
or boops when it is taken).  The machine outputs the number of beeps strictly between each two
consecutive boops.  If some output value occurs infinitely often, the machine
*pseudoquasihalts*, and `g(M)` is the number of transitions it takes to finish outputting such
a value for the first time: the step count up to and including the boop that closes the first
interval whose value occurs infinitely often.  `BBBB(n)` is the largest finite `g(M)`.

Steps are numbered from `0`: step `k` is the `(k+1)`-th transition, so an interval closed by
the boop at step `j` gives `g = j + 1`.

The wiki lists three models: arbitrary sets of beep and boop transitions, exactly one beep and
one boop transition, and one boop transition with every other transition a beep.  We define
`g` for arbitrary sets (`Machine.QQHaltsAt`), and the other two models restrict the sets
(`Main.lean`).
-/

namespace Bbbb

open TM

/-- An `n`-state, 2-symbol Turing machine; `none` is a halting (undefined) transition. -/
abbrev Machine (n : Nat) := Fin n → Bool → Option (Bool × Dir × Fin n)

/-- A set of transitions (state × symbol read), as a predicate. -/
abbrev TSet (n : Nat) := Fin n → Bool → Bool

/-- The transition taken at step `k` of the run from `c`, `none` if there is none (the machine
halted at or before step `k`). -/
def labFrom {Q : Type} (M : Q → Bool → Option (Bool × Dir × Q)) (c : Cfg Q) (k : Nat) :
    Option (Q × Bool) :=
  match run M k c with
  | none => none
  | some d => if (M d.q (d.R 0)).isSome then some (d.q, d.R 0) else none

/-- The start configuration: state `0`, blank tape. -/
def init {n : Nat} : Cfg (Fin (n + 1)) := ⟨0, blank, blank⟩

/-- The transition taken at step `k` from the start. -/
def lab {n : Nat} (M : Machine (n + 1)) (k : Nat) : Option (Fin (n + 1) × Bool) :=
  labFrom M init k

/-- Step `k` is an event of the transition set `S` (a beep for the beep set, a boop for the
boop set). -/
def ev {n : Nat} (S : TSet (n + 1)) (M : Machine (n + 1)) (k : Nat) : Bool :=
  match lab M k with
  | none => false
  | some (q, b) => S q b

/-! ## Output values of a beep sequence and a boop sequence -/

/-- the number of `k` in `[a, b)` with `f k` -/
def count (f : Nat → Bool) (a b : Nat) : Nat :=
  ((List.range (b - a)).filter (fun k => f (a + k))).length

/-- `i < j` are consecutive boops. -/
structure IsInterval (bo : Nat → Bool) (i j : Nat) : Prop where
  lt : i < j
  left : bo i = true
  right : bo j = true
  between : ∀ k, i < k → k < j → bo k = false

/-- the output of an interval: the number of beeps strictly between its boops -/
def value (be : Nat → Bool) (i j : Nat) : Nat := count be (i + 1) j

/-- the value `v` is output infinitely often -/
def InfinitelyRepeated (be bo : Nat → Bool) (v : Nat) : Prop :=
  ∀ N, ∃ i j, N ≤ i ∧ IsInterval bo i j ∧ value be i j = v

/-- `g = t`: `t - 1` is the closing boop of the first interval whose value is output
infinitely often. -/
def QQHaltsAt (be bo : Nat → Bool) (t : Nat) : Prop :=
  ∃ i j, IsInterval bo i j ∧ InfinitelyRepeated be bo (value be i j) ∧ t = j + 1 ∧
    ∀ i' j', IsInterval bo i' j' → InfinitelyRepeated be bo (value be i' j') → j ≤ j'

/-- `g(M) = t` for the machine `M` with beep set `B` and boop set `O`. -/
def Machine.QQHaltsAt {n : Nat} (M : Machine (n + 1)) (B O : TSet (n + 1)) (t : Nat) : Prop :=
  Bbbb.QQHaltsAt (ev B M) (ev O M) t

/-- `BBBB(n) = t` in the model where the allowed (beep set, boop set) pairs are those
satisfying `model`: every finite `g` is at most `t`, and some machine has `g = t`. -/
def IsBBBB (n : Nat) (model : TSet (n + 1) → TSet (n + 1) → Prop) (t : Nat) : Prop :=
  (∀ (M : Machine (n + 1)) (B O : TSet (n + 1)) (s : Nat), model B O → M.QQHaltsAt B O s → s ≤ t) ∧
    ∃ (M : Machine (n + 1)) (B O : TSet (n + 1)), model B O ∧ M.QQHaltsAt B O t

/-! ## The three models -/

/-- arbitrary sets of beep and boop transitions -/
def anySets {n : Nat} (_ _ : TSet (n + 1)) : Prop := True

/-- exactly one beep transition and exactly one boop transition -/
def oneEach {n : Nat} (B O : TSet (n + 1)) : Prop :=
  ∃ qb bb qo bo, (∀ q b, B q b = (q == qb && b == bb)) ∧ (∀ q b, O q b = (q == qo && b == bo))

/-- one boop transition, every other transition beeps -/
def oneBoopRestBeep {n : Nat} (B O : TSet (n + 1)) : Prop :=
  ∃ qo bo, (∀ q b, O q b = (q == qo && b == bo)) ∧ (∀ q b, B q b = !(q == qo && b == bo))

end Bbbb
