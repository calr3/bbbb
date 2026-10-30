import Bbbb.Codes

/-!
# The witness: `0RB1LB_1LA1RB`, beep A0, boop A1, has `g = 18`

Its transitions are `A0 B0 A0 B1 B0 A1 B0 A0`, then `B1 B1 B1 B0 A1` forever (a translated
cycler).  The boops are at steps 5, 12, 17, 22, …; the first interval (5, 12) has one beep
(A0 at step 7), every later interval none.  So the value 0 is output forever, first by the
interval (12, 17), and `g = 18`.  The other beep sets of the champions work the same way.
-/

namespace Bbbb

open TM

/-- `0RB1LB_1LA1RB` -/
def champ : Machine 2 := ofCodes2 2 8 7 6

/-- one transition as a set -/
def single {n : Nat} (q : Fin (n + 1)) (b : Bool) : TSet (n + 1) := fun q' b' => q' == q && b' == b

def champPre : List (Fin 2 × Bool) :=
  [(0, false), (1, false), (0, false), (1, true), (1, false), (0, true), (1, false), (0, false)]

def champPer : List (Fin 2 × Bool) := [(1, true), (1, true), (1, true), (1, false), (0, true)]

theorem champ_lab : ∀ k, lab champ k = seqv champPre champPer k :=
  lab_eq_seqv (t0 := 8) (p := 5) (kl := .any) (kr := .blank)
    (wc := ⟨1, [false], [true, true, true]⟩) (w0 := ⟨1, [], [true, true, true]⟩)
    (w1 := ⟨1, [true], [true, true, true]⟩) (by decide) rfl rfl (by decide) (by decide)
    rfl rfl (by decide) (by decide)

theorem value_zero {be : Nat → Bool} {T i j : Nat} (h : ∀ k, T ≤ k → be k = false) (hi : T ≤ i) :
    value be i j = 0 :=
  count_eq_zero (fun k h1 _ => h k (by omega))

theorem interval_unique {bo : Nat → Bool} {i j j' : Nat} (h : IsInterval bo i j)
    (h' : IsInterval bo i j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with hl | he | hl
  · have := h'.between j h.lt hl; rw [h.right] at this; cases this
  · exact he
  · have := h.between j' h'.lt hl; rw [h'.right] at this; cases this

theorem champ_ev (S : TSet 2) (k : Nat) : ev S champ k = evq S (seqv champPre champPer k) := by
  rw [ev_eq, champ_lab]

theorem champ_per (S : TSet 2) : Periodic (ev S champ) 8 5 := by
  intro k hk
  rw [champ_ev, champ_ev]
  exact congrArg _ (seqv_periodic champPre champPer k hk)

theorem champ_seqv (k : Nat) (hk : 8 ≤ k) : seqv champPre champPer k = champPer[(k - 8) % 5]? := by
  unfold seqv; rw [if_neg (by simp [champPre]; omega)]; rfl

/-- the boops up to step 17 -/
theorem champ_bo_lt (k : Nat) (hk : k < 18) :
    ev (single 0 true) champ k = (k == 5 || k == 12 || k == 17) := by
  rw [champ_ev]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ => decide
  | _ + 18, hk => exact absurd hk (by omega)

/-- the boops from step 8 on: steps `12 + 5m` -/
theorem champ_bo_ge (k : Nat) (hk : 8 ≤ k) (h : ev (single 0 true) champ k = true) :
    (k - 12) % 5 = 0 ∧ 12 ≤ k := by
  rw [champ_ev, champ_seqv k hk] at h
  have : (k - 8) % 5 < 5 := Nat.mod_lt _ (by decide)
  match e : (k - 8) % 5, this with
  | 0, _ | 1, _ | 2, _ | 3, _ => rw [e] at h; simp [champPer, evq, single] at h
  | 4, _ => omega

theorem champ_I : IsInterval (ev (single 0 true) champ) 12 17 := by
  refine ⟨by decide, by rw [champ_bo_lt 12 (by decide)]; rfl,
    by rw [champ_bo_lt 17 (by decide)]; rfl, ?_⟩
  intro k h1 h2
  rw [champ_bo_lt k (by omega)]
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  omega

/-- every interval from step 12 on outputs the value of the interval (12, 17) -/
theorem champ_late (B : TSet 2) {i j : Nat} (hi : 12 ≤ i)
    (hI : IsInterval (ev (single 0 true) champ) i j) :
    value (ev B champ) i j = value (ev B champ) 12 17 := by
  obtain ⟨hm, _⟩ := champ_bo_ge i (by omega) hI.left
  obtain ⟨hI2, hv⟩ := interval_shift (champ_per B) (champ_per _) ((i - 12) / 5) (by decide)
    champ_I
  have e : 12 + (i - 12) / 5 * 5 = i := by
    have := Nat.div_add_mod (i - 12) 5; rw [Nat.mul_comm] at this; omega
  rw [e] at hI2 hv
  rw [← interval_unique hI2 hI, hv]

/-- With boop A1, `g = 18` for every beep set whose first value differs from the later ones. -/
theorem champ_qq (B : TSet 2) (hne : value (ev B champ) 5 12 ≠ value (ev B champ) 12 17) :
    champ.QQHaltsAt B (single 0 true) 18 := by
  have hI := champ_I
  refine ⟨12, 17, hI, rep_of_periodic (by decide) (champ_per B) (champ_per _) (by decide) hI,
    rfl, ?_⟩
  intro i' j' hI' hr'
  apply Classical.byContradiction
  intro hlt
  have hi'5 : i' = 5 ∧ j' = 12 := by
    have h1 := hI'.left
    have h2 := hI'.right
    have h3 := hI'.lt
    rw [champ_bo_lt i' (by omega)] at h1
    rw [champ_bo_lt j' (by omega)] at h2
    simp only [Bool.or_eq_true, beq_iff_eq] at h1 h2
    omega
  obtain ⟨rfl, rfl⟩ := hi'5
  obtain ⟨i, j, hi, hIij, hval⟩ := hr' 12
  rw [champ_late B hi hIij] at hval
  exact hne hval.symm

/-- the value of an interval of the champion, computed -/
theorem champ_value (B : TSet 2) (i j : Nat) :
    value (ev B champ) i j =
      ((List.range (j - (i + 1))).filter (fun k => evq B (seqv champPre champPer (i + 1 + k)))).length := by
  unfold value count; simp only [champ_ev]

end Bbbb
