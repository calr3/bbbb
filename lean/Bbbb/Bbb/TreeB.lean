import Bbbb.Bbb.Rec

/-!
# Trees of partial machines for BBB

As in `Tree.lean`: a node runs the partial machine to an undefined transition after `t` steps and
branches on its choices; the halting choice beeps last at step at most `t + 1`.  A leaf is a
translated cycler (`checkLeafB`) or carries a recurrence certificate (`checkACert`); holdouts are
proved separately.
-/

namespace Bbbb

open TM

inductive TreeB (n : Nat)
  | leaf (c : Cert)
  | recur (c : ACert n)
  | hold (k : Nat)
  | node (t : Nat) (kids : List (TreeB n))

mutual
def checkTreeB (n K : Nat) (hl : List PM) : PM → TreeB n → Bool
  | P, .leaf c => checkLeafB (P.toM n) K c
  | P, .recur c => checkACert (P.toM n) K c
  | P, .hold k => decide (hl[k]? = some P)
  | P, .node t kids => decide (t + 1 ≤ K) && match haltIdx (P.toM n) t with
    | some i => decide (P[i]? = some none) && checkKidsB n K hl P i 1 kids
    | none => false
def checkKidsB (n K : Nat) (hl : List PM) : PM → Nat → Nat → List (TreeB n) → Bool
  | _, _, c, [] => decide (c = 4 * (n + 1) + 1)
  | P, i, c, k :: ks => checkTreeB n K hl (P.set i (some c)) k && checkKidsB n K hl P i (c + 1) ks
end

/-- every machine extending `P` beeps last at step at most `K` -/
def CoveredB (n K : Nat) (P : PM) : Prop := ∀ M : Machine (n + 1), Ext M P → GoodB M K

mutual
theorem checkTreeB_sound {n K : Nat} {hl : List PM}
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    (hh : ∀ (k : Nat) (P : PM), hl[k]? = some P → CoveredB n K P) :
    ∀ (P : PM) (T : TreeB n), checkTreeB n K hl P T = true → CoveredB n K P
  | P, .leaf c, h => fun _ hM => by
    have := checkLeafB_sound (by simpa [checkTreeB] using h)
    exact goodB_ext this.2 this.1 hM
  | P, .recur c, h => fun _ hM => by
    have := checkACert_sound (by simpa [checkTreeB] using h)
    exact goodB_ext this.2 this.1 hM
  | P, .hold k, h => hh k P (by simpa [checkTreeB] using h)
  | P, .node t kids, h => by
    simp only [checkTreeB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hK, h⟩ := h
    cases hi : haltIdx (P.toM n) t with
    | none => rw [hi] at h; cases h
    | some i =>
      rw [hi] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun M hM => goodB_of_node hi h.1 hK
        (fun c h1 h2 => checkKidsB_sound hsurj hh P i 1 kids h.2 c h1 h2) hsurj hM
theorem checkKidsB_sound {n K : Nat} {hl : List PM}
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    (hh : ∀ (k : Nat) (P : PM), hl[k]? = some P → CoveredB n K P) :
    ∀ (P : PM) (i c : Nat) (kids : List (TreeB n)), checkKidsB n K hl P i c kids = true →
      ∀ c', c ≤ c' → c' < 4 * (n + 1) + 1 → CoveredB n K (P.set i (some c'))
  | _, _, c, [], h => fun c' h1 h2 => by
    simp only [checkKidsB, decide_eq_true_eq] at h; omega
  | P, i, c, k :: ks, h => fun c' h1 h2 => by
    simp only [checkKidsB, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact checkTreeB_sound hsurj hh _ k h.1
    · exact checkKidsB_sound hsurj hh P i (c + 1) ks h.2 c' e h2
end

/-! ## forests -/

def checkForestB (n K : Nat) (hl : List PM) (F : List (PM × TreeB n)) : Bool :=
  F.all (fun x => checkTreeB n K hl x.1 x.2)

theorem checkForestB_sound {n K : Nat} {hl : List PM}
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    (hh : ∀ (k : Nat) (P : PM), hl[k]? = some P → CoveredB n K P) {F : List (PM × TreeB n)}
    (h : checkForestB n K hl F = true) : ∀ x ∈ F, CoveredB n K x.1 := by
  intro x hx
  unfold checkForestB at h
  rw [List.all_eq_true] at h
  exact checkTreeB_sound hsurj hh _ _ (h x hx)

theorem forestsB_covered {n K : Nat} {Fs : List (List (PM × TreeB n))}
    (h : ∀ F ∈ Fs, ∀ x ∈ F, CoveredB n K x.1) : ∀ P ∈ (Fs.flatten.map Prod.fst), CoveredB n K P := by
  intro P hP
  simp only [List.mem_map, List.mem_flatten] at hP
  obtain ⟨x, ⟨F, hF, hx⟩, rfl⟩ := hP
  exact h F hF x hx

theorem coveredB_of_mem {n K : Nat} {l : List PM} (h : ∀ P ∈ l, CoveredB n K P) :
    ∀ (k : Nat) (P : PM), l[k]? = some P → CoveredB n K P :=
  fun _ P e => h P (List.mem_of_getElem? e)

end Bbbb
