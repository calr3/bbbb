/-!
# Deterministic partial step systems

Both Turing machines and counter machines are instances: a configuration either
steps to a unique successor or halts (`none`).
-/

namespace Sys

variable {α : Type} (f : α → Option α)

/-- `run n c` : configuration after `n` steps, `none` if it halted before. -/
def run : Nat → α → Option α
  | 0, c => some c
  | n + 1, c => match f c with
    | none => none
    | some c' => run n c'

def Reach (a b : α) : Prop := ∃ n, run f n a = some b
def Reach1 (a b : α) : Prop := ∃ n, run f (n + 1) a = some b
def Halts (a : α) : Prop := ∃ n, run f n a = none

variable {f}

theorem run_add (a b : Nat) (c : α) : run f (a + b) c = (run f a c).bind (run f b) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.add_right_comm]; simp only [run]
    cases f c with
    | none => rfl
    | some c' => exact ih c'

theorem run_none_mono {n : Nat} {c : α} (h : run f n c = none) (m : Nat) :
    run f (n + m) c = none := by
  rw [run_add, h]; rfl

theorem Reach.refl (c : α) : Reach f c c := ⟨0, rfl⟩

theorem Reach.trans {a b c : α} : Reach f a b → Reach f b c → Reach f a c := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩; exact ⟨m + n, by rw [run_add, hm]; exact hn⟩

theorem Reach.single {a b : α} (h : f a = some b) : Reach f a b := ⟨1, by simp [run, h]⟩

theorem Reach1.single {a b : α} (h : f a = some b) : Reach1 f a b := ⟨0, by simp [run, h]⟩

theorem Reach1.reach {a b : α} : Reach1 f a b → Reach f a b := fun ⟨n, h⟩ => ⟨n + 1, h⟩

theorem Reach1.trans_reach {a b c : α} : Reach1 f a b → Reach f b c → Reach1 f a c := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩; exact ⟨m + n, by rw [Nat.add_right_comm, run_add, hm]; exact hn⟩

theorem Reach.trans_reach1 {a b c : α} : Reach f a b → Reach1 f b c → Reach1 f a c := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩; exact ⟨m + n, by rw [Nat.add_assoc, run_add, hm]; exact hn⟩

theorem Reach1.trans {a b c : α} (h1 : Reach1 f a b) (h2 : Reach1 f b c) : Reach1 f a c :=
  h1.trans_reach h2.reach

theorem Reach1.of_step {a b c : α} (h : f a = some b) (h' : Reach f b c) : Reach1 f a c :=
  (Reach1.single h).trans_reach h'

theorem Halts.of_step {a : α} (h : f a = none) : Halts f a := ⟨1, by simp [run, h]⟩

theorem Reach.halts {a b : α} : Reach f a b → Halts f b → Halts f a := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩; exact ⟨m + n, by rw [run_add, hm]; exact hn⟩

theorem run_some_of_le {m n : Nat} {a b : α} (h : run f n a = some b) (hmn : m ≤ n) :
    ∃ c, run f m a = some c := by
  cases hm : run f m a with
  | some c => exact ⟨c, rfl⟩
  | none =>
    have := run_none_mono hm (n - m)
    rw [Nat.add_sub_cancel' hmn, h] at this; exact absurd this (by simp)

/-- Determinism: halting is inherited along reachability. -/
theorem Halts.of_reach {a b : α} (hr : Reach f a b) (hh : Halts f a) : Halts f b := by
  obtain ⟨m, hm⟩ := hr; obtain ⟨n, hn⟩ := hh
  by_cases hle : n ≤ m
  · have := run_none_mono hn (m - n)
    rw [Nat.add_sub_cancel' hle, hm] at this; exact absurd this (by simp)
  · refine ⟨n - m, ?_⟩
    have := run_add (f := f) m (n - m) a
    rw [Nat.add_sub_cancel' (by omega), hm, hn] at this
    exact this.symm

theorem Reach.halts_iff {a b : α} (hr : Reach f a b) : Halts f a ↔ Halts f b :=
  ⟨fun h => h.of_reach hr, fun h => hr.halts h⟩

/-- If from every configuration in a family we strictly reach another member,
no member halts. -/
theorem not_halts_of_progress (P : α → Prop)
    (hP : ∀ c, P c → ∃ c', P c' ∧ Reach1 f c c') :
    ∀ c, P c → ¬ Halts f c := by
  intro c hc ⟨N, hN⟩
  have key : ∀ k, ∀ c, P c → ∃ n c', k ≤ n ∧ run f n c = some c' := by
    intro k
    induction k with
    | zero => intro c _; exact ⟨0, c, Nat.le_refl _, rfl⟩
    | succ k ih =>
      intro c hc
      obtain ⟨c', hc', m, hm⟩ := hP c hc
      obtain ⟨n, c'', hk, hn⟩ := ih c' hc'
      exact ⟨m + 1 + n, c'', by omega, by rw [run_add, hm]; exact hn⟩
  obtain ⟨n, c', hk, hn⟩ := key N c hc
  have := run_none_mono hN (n - N)
  rw [Nat.add_sub_cancel' hk, hn] at this
  exact Option.noConfusion this

end Sys
