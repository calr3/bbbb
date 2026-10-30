import Bbbb.Core.Sys

/-!
# Turing machine semantics on stream tapes

A tape side is a stream `Nat → Bool` (all but finitely many cells blank in
practice).  A configuration stores the state, the left side (nearest cell
first) and the right side, whose first cell is the cell under the head.
-/

namespace TM

abbrev Strm := Nat → Bool

def blank : Strm := fun _ => false

def cons (b : Bool) (s : Strm) : Strm := fun n => match n with
  | 0 => b
  | n + 1 => s n

infixr:67 " ::: " => cons

def tl (s : Strm) : Strm := fun n => s (n + 1)

/-- `ones n s` : n cells containing 1, then `s`. -/
def ones : Nat → Strm → Strm
  | 0, s => s
  | n + 1, s => true ::: ones n s

@[simp] theorem cons_zero (b : Bool) (s : Strm) : (b ::: s) 0 = b := rfl
@[simp] theorem tl_cons (b : Bool) (s : Strm) : tl (b ::: s) = s := rfl
@[simp] theorem ones_zero (s : Strm) : ones 0 s = s := rfl
theorem ones_succ (n : Nat) (s : Strm) : ones (n + 1) s = true ::: ones n s := rfl

@[simp] theorem tl_blank : tl blank = blank := rfl

theorem cons_blank : false ::: blank = blank := by
  funext n; cases n <;> rfl

theorem cons_head_tl (s : Strm) : s 0 ::: tl s = s := by
  funext n; cases n <;> rfl

theorem ones_add (a b : Nat) (s : Strm) : ones a (ones b s) = ones (a + b) s := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.add_right_comm, ones_succ, ones_succ, ih]

theorem ones_succ' (n : Nat) (s : Strm) : ones (n + 1) s = ones n (true ::: s) := by
  exact (ones_add n 1 s).symm

theorem ones_cons_true (n : Nat) (s : Strm) : ones n (true ::: s) = true ::: ones n s := by
  rw [← ones_succ', ones_succ]

/-- `zeros n s` : n blank cells, then `s`. -/
def zeros : Nat → Strm → Strm
  | 0, s => s
  | n + 1, s => false ::: zeros n s

theorem zeros_succ' (n : Nat) (s : Strm) : zeros (n + 1) s = zeros n (false ::: s) := by
  induction n with
  | zero => rfl
  | succ n ih => show false ::: zeros (n+1) s = false ::: zeros n (false ::: s); rw [ih]

theorem zeros_add (a b : Nat) (s : Strm) : zeros a (zeros b s) = zeros (a + b) s := by
  induction a with
  | zero => simp [zeros]
  | succ a ih => rw [Nat.add_right_comm]; show false ::: zeros a (zeros b s) = false ::: zeros (a + b) s; rw [ih]

theorem zeros_cons_false (n : Nat) (s : Strm) : zeros n (false ::: s) = false ::: zeros n s := by
  rw [← zeros_succ']; rfl

@[simp] theorem zeros_blank (n : Nat) : zeros n blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => show false ::: zeros n blank = blank; rw [ih, cons_blank]

inductive Dir | L | R
deriving DecidableEq

structure Cfg (Q : Type) where
  q : Q
  L : Strm
  R : Strm

variable {Q : Type} (δ : Q → Bool → Option (Bool × Dir × Q))

def step (c : Cfg Q) : Option (Cfg Q) :=
  match δ c.q (c.R 0) with
  | none => none
  | some (w, Dir.R, q') => some ⟨q', w ::: c.L, tl c.R⟩
  | some (w, Dir.L, q') => some ⟨q', tl c.L, c.L 0 ::: w ::: tl c.R⟩

/-! The run, reachability and halting of a machine are those of the step
system `step δ` (`Bbbb.Core.Sys`); the lemmas below restate the `Sys` ones
with the transition function as an explicit argument. -/

/-- `run n c` : configuration after `n` steps, `none` if it halted before. -/
abbrev run : Nat → Cfg Q → Option (Cfg Q) := Sys.run (step δ)
abbrev Reach (c c' : Cfg Q) : Prop := Sys.Reach (step δ) c c'
/-- Strict reachability (at least one step), used for non-termination. -/
abbrev Reach1 (c c' : Cfg Q) : Prop := Sys.Reach1 (step δ) c c'
abbrev Halts (c : Cfg Q) : Prop := Sys.Halts (step δ) c

theorem run_zero (c : Cfg Q) : run δ 0 c = some c := rfl

theorem run_add (a b : Nat) (c : Cfg Q) :
    run δ (a + b) c = (run δ a c).bind (run δ b) := Sys.run_add a b c

theorem Reach.refl (c : Cfg Q) : Reach δ c c := Sys.Reach.refl c

theorem Reach.trans {a b c : Cfg Q} : Reach δ a b → Reach δ b c → Reach δ a c := Sys.Reach.trans

theorem Reach.halts {a b : Cfg Q} : Reach δ a b → Halts δ b → Halts δ a := Sys.Reach.halts

theorem halts_of_step {c : Cfg Q} (h : step δ c = none) : Halts δ c := Sys.Halts.of_step h

theorem run_none_mono {n : Nat} {c : Cfg Q} (h : run δ n c = none) (m : Nat) :
    run δ (n + m) c = none := Sys.run_none_mono h m

theorem reach_step {c c' : Cfg Q} (h : step δ c = some c') : Reach δ c c' := Sys.Reach.single h

theorem Reach1.of_step_reach {c c' c'' : Cfg Q} (h : step δ c = some c')
    (h' : Reach δ c' c'') : Reach1 δ c c'' := Sys.Reach1.of_step h h'

theorem Reach1.reach {c c' : Cfg Q} : Reach1 δ c c' → Reach δ c c' := Sys.Reach1.reach

theorem Reach1.trans_reach {a b c : Cfg Q} : Reach1 δ a b → Reach δ b c → Reach1 δ a c :=
  Sys.Reach1.trans_reach

theorem Reach.trans_reach1 {a b c : Cfg Q} : Reach δ a b → Reach1 δ b c → Reach1 δ a c :=
  Sys.Reach.trans_reach1

/-- If from every configuration in a family we strictly reach another member
of the family, the machine never halts from any member. -/
theorem not_halts_of_progress (P : Cfg Q → Prop)
    (hP : ∀ c, P c → ∃ c', P c' ∧ Reach1 δ c c') :
    ∀ c, P c → ¬ Halts δ c := Sys.not_halts_of_progress P hP

end TM

namespace TM

/-! ## Simulation: a machine that agrees on all used transitions -/

def Compat {Q Q' : Type} (φ : Q → Q') : Option (Bool × Dir × Q) → Option (Bool × Dir × Q') → Prop
  | none, _ => True
  | some (w, d, q), x => x = some (w, d, φ q)

def Cfg.map {Q Q' : Type} (φ : Q → Q') (c : Cfg Q) : Cfg Q' := ⟨φ c.q, c.L, c.R⟩

theorem sim_run {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) :
    ∀ n (c c' : Cfg Q), run δ n c = some c' → run δ' n (c.map φ) = some (c'.map φ) := by
  intro n
  induction n with
  | zero => intro c c' hc; simp [run, Sys.run] at hc ⊢; rw [hc]
  | succ n ih =>
    intro c c' hc
    simp only [run, Sys.run] at hc ⊢
    have hq := h c.q (c.R 0)
    unfold step at hc ⊢
    simp only [Cfg.map]
    revert hc hq
    cases δ c.q (c.R 0) with
    | none => intro hc; exact absurd hc (by simp)
    | some t =>
      obtain ⟨w, d, q⟩ := t
      intro hc hq
      simp only [Compat] at hq
      rw [hq]
      cases d with
      | R => exact ih _ _ hc
      | L => exact ih _ _ hc

/-- Transfer of a halting theorem to a machine that simulates the original
(e.g. one obtained by merging states): it halts iff the original does, provided
the original only halts by reaching a configuration where the simulator halts. -/
theorem halts_iff_of_sim {Q Q' : Type} (δ : Q → Bool → Option (Bool × Dir × Q))
    (δ' : Q' → Bool → Option (Bool × Dir × Q')) (φ : Q → Q')
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) (s : Cfg Q) {P : Prop}
    (hiff : Halts δ s ↔ P) (hhalt : P → ∃ c, Reach δ s c ∧ δ' (φ c.q) (c.R 0) = none) :
    Halts δ' (s.map φ) ↔ P := by
  constructor
  · intro ⟨N, hN⟩
    apply Classical.byContradiction; intro hno
    cases hr : run δ N s with
    | none => exact hno (hiff.1 ⟨N, hr⟩)
    | some c =>
      have := sim_run δ δ' φ h N s c hr
      exact Option.noConfusion (this.symm.trans hN)
  · intro hp
    obtain ⟨c, ⟨n, hn⟩, hq⟩ := hhalt hp
    have hs := sim_run δ δ' φ h n s c hn
    refine Reach.halts δ' ⟨n, hs⟩ (halts_of_step δ' ?_)
    simp [step, Cfg.map, hq]

end TM
