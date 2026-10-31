import Bbbb.Holdouts.Seg

/-!
# Shift rules: crossing `k` copies of a word

The bouncer certificates (`tools/bbbb3/bouncer.py`) cross a block `w^k` with one checked run over
a single copy of `w`.  These lemmas turn such a run into a run over `k` copies, for every `k`.

* `seg_shift`: the context `c` on the left is left as it was, and the copy becomes `w2` in front
  of it (`c ++ X` becomes `w2 ++ c ++ X`, and `w2 ++ c` starts with `c`);
* `seg_shift_carry`: the context travels with the head (`c ++ X` becomes `c ++ w2 ++ X`).

Both take a tail `Y` after the copies; with `Y` starting with one more copy of `w` they are the
rules with lookahead.
-/

namespace Bbbb

open TM

variable {Q : Type}

/-- `w` repeated `k` times -/
def wpow (w : List Bool) : Nat → List Bool
  | 0 => []
  | k + 1 => w ++ wpow w k

theorem wpow_succ' (w : List Bool) (k : Nat) : wpow w (k + 1) = wpow w k ++ w := by
  induction k with
  | zero => simp [wpow]
  | succ k ih =>
    show w ++ wpow w (k + 1) = (w ++ wpow w k) ++ w
    rw [ih, List.append_assoc]

/-- labels repeated `k` times -/
def lpow {α : Type} (l : List α) : Nat → List α
  | 0 => []
  | k + 1 => l ++ lpow l k

/-- The context `c` stays, a copy of `w` becomes `w2` in front of it.  `hrun` is the run over one
copy, for every left tail `X` and right tail `Y`; `hc`: `w2 ++ c` starts with `c`. -/
theorem seg_shift {M : Q → Bool → Option (Bool × Dir × Q)} {q : Q} {c w w2 e : List Bool}
    {ls : List (Q × Bool)} (hc : w2 ++ c = c ++ e)
    (hrun : ∀ X Y, Seg M ⟨q, app c X, app w Y⟩ ls ⟨q, app (w2 ++ c) X, Y⟩) :
    ∀ k X Y, Seg M ⟨q, app c X, app (wpow w k) Y⟩ (lpow ls k)
      ⟨q, app (wpow w2 k) (app c X), Y⟩ := by
  intro k
  induction k with
  | zero => intro X Y; exact Seg.nil M _
  | succ k ih =>
    intro X Y
    have h1 := hrun X (app (wpow w k) Y)
    rw [hc, app_append] at h1
    have h2 := ih (app e X) Y
    refine Seg.congr (h1.trans h2) (by simp [wpow, app_append]) ?_ rfl
    rw [wpow_succ', app_append, ← app_append c e, ← hc, app_append]

/-- The context `c` travels with the head: `c ++ X` becomes `c ++ w2 ++ X`. -/
theorem seg_shift_carry {M : Q → Bool → Option (Bool × Dir × Q)} {q : Q} {c w w2 : List Bool}
    {ls : List (Q × Bool)}
    (hrun : ∀ X Y, Seg M ⟨q, app c X, app w Y⟩ ls ⟨q, app c (app w2 X), Y⟩) :
    ∀ k X Y, Seg M ⟨q, app c X, app (wpow w k) Y⟩ (lpow ls k)
      ⟨q, app c (app (wpow w2 k) X), Y⟩ := by
  intro k
  induction k with
  | zero => intro X Y; exact Seg.nil M _
  | succ k ih =>
    intro X Y
    have h1 := hrun X (app (wpow w k) Y)
    have h2 := ih (app w2 X) Y
    refine Seg.congr (h1.trans h2) (by simp [wpow, app_append]) ?_ rfl
    rw [wpow_succ', app_append]

/-- A window run over one copy (both tails arbitrary) is a run for every pair of tails. -/
theorem seg_of_wrun {M : Q → Bool → Option (Bool × Dir × Q)} {m : Nat} {w0 w1 : Win Q}
    {ls : List (Q × Bool)} (h : wrun M .any .any m w0 = some (w1, ls)) (X Y : Strm) :
    Seg M (w0.den X Y) ls (w1.den X Y) := by
  obtain ⟨hrun, hlen, hlab⟩ := wrun_sound (kl := .any) (kr := .any) (X := X) (Y := Y)
    trivial trivial m w0 w1 ls h
  exact ⟨by rw [hlen]; exact hrun, fun k hk => hlab k (by omega)⟩

end Bbbb
