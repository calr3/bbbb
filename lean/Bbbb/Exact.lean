import Bbbb.Witness

/-!
# The exact `g` of an eventually periodic machine

If the transitions are `pre`, then `per` repeated, a value is output forever iff it is the value
of an interval starting in the first period after the preperiod (`rep_iff`).  So `g` is decided
by a finite computation (`qq_of_check`), used for the champions.
-/

namespace Bbbb

open TM

/-- `i < j` are consecutive boops (computably) -/
def isIntB (bo : Nat → Bool) (i j : Nat) : Bool :=
  decide (i < j) && bo i && bo j && (List.range (j - i - 1)).all (fun d => !bo (i + 1 + d))

theorem isIntB_iff {bo : Nat → Bool} {i j : Nat} : isIntB bo i j = true ↔ IsInterval bo i j := by
  unfold isIntB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun k a b => by
      have := h4 (k - i - 1) (by omega); rwa [show i + 1 + (k - i - 1) = k by omega] at this⟩
  · intro h
    exact ⟨⟨⟨h.lt, h.left⟩, h.right⟩, fun d hd => h.between _ (by omega) (by omega)⟩

section periodic

variable {be bo : Nat → Bool} {t0 p : Nat} (hp : 0 < p) (hb : Periodic be t0 p)
  (ho : Periodic bo t0 p)
include hp hb ho

/-- an interval one period later moves back one period -/
theorem interval_unshift {i j : Nat} (hi : t0 + p ≤ i) (hI : IsInterval bo i j) :
    IsInterval bo (i - p) (j - p) ∧ value be (i - p) (j - p) = value be i j := by
  have hlt := hI.lt
  have := interval_shift hb ho 1 (i := i - p) (j := j - p) (by omega) ⟨by omega,
    by rw [← ho _ (by omega), show i - p + p = i by omega]; exact hI.left,
    by rw [← ho _ (by omega), show j - p + p = j by omega]; exact hI.right,
    fun k h1 h2 => by rw [← ho _ (by omega)]; exact hI.between _ (by omega) (by omega)⟩
  simp only [Nat.one_mul, show i - p + p = i by omega, show j - p + p = j by omega] at this
  exact ⟨⟨by omega, by rw [← ho _ (by omega), show i - p + p = i by omega]; exact hI.left,
    by rw [← ho _ (by omega), show j - p + p = j by omega]; exact hI.right,
    fun k h1 h2 => by rw [← ho _ (by omega)]; exact hI.between _ (by omega) (by omega)⟩,
    this.2.symm⟩

/-- every interval after the preperiod has the value of one in the first period -/
theorem interval_first {i j : Nat} (hi : t0 ≤ i) (hI : IsInterval bo i j) :
    ∃ i' j', t0 ≤ i' ∧ i' < t0 + p ∧ j' ≤ i' + p ∧ IsInterval bo i' j' ∧
      value be i' j' = value be i j := by
  induction i using Nat.strongRecOn generalizing j with
  | ind i ih =>
    by_cases h : i < t0 + p
    · refine ⟨i, j, hi, h, ?_, hI, rfl⟩
      apply Classical.byContradiction; intro hj
      have := hI.between (i + p) (by omega) (by omega)
      rw [ho i hi, hI.left] at this; cases this
    · obtain ⟨hI', hv⟩ := interval_unshift hp hb ho (by omega) hI
      obtain ⟨i', j', h1, h2, h3, h4, h5⟩ := ih (i - p) (by omega) (by omega) hI'
      exact ⟨i', j', h1, h2, h3, h4, h5.trans hv⟩

theorem rep_iff {v : Nat} : InfinitelyRepeated be bo v ↔
    ∃ i' j', t0 ≤ i' ∧ i' < t0 + p ∧ j' ≤ i' + p ∧ IsInterval bo i' j' ∧ value be i' j' = v := by
  constructor
  · intro h
    obtain ⟨i, j, hi, hI, hv⟩ := h t0
    obtain ⟨i', j', h1, h2, h3, h4, h5⟩ := interval_first hp hb ho hi hI
    exact ⟨i', j', h1, h2, h3, h4, h5.trans hv⟩
  · rintro ⟨i', j', h1, _, _, h4, rfl⟩
    exact rep_of_periodic hp hb ho h1 h4

end periodic

/-! ## the computation -/

/-- the values of the intervals starting in the first period -/
def perVals (be bo : Nat → Bool) (t0 p : Nat) : List Nat :=
  (List.range p).flatMap (fun a => (List.range (p + 1)).filterMap (fun d =>
    if isIntB bo (t0 + a) (t0 + a + d) then some (value be (t0 + a) (t0 + a + d)) else none))

theorem mem_perVals {be bo : Nat → Bool} {t0 p v : Nat} :
    v ∈ perVals be bo t0 p ↔ ∃ i' j', t0 ≤ i' ∧ i' < t0 + p ∧ j' ≤ i' + p ∧
      IsInterval bo i' j' ∧ value be i' j' = v := by
  unfold perVals
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq]
  constructor
  · rintro ⟨a, ha, d, hd, hI, rfl⟩
    exact ⟨_, _, by omega, by omega, by omega, isIntB_iff.1 hI, rfl⟩
  · rintro ⟨i', j', h1, h2, h3, hI, rfl⟩
    have hlt := hI.lt
    refine ⟨i' - t0, by omega, j' - i', by omega, ?_⟩
    rw [show t0 + (i' - t0) = i' by omega, show i' + (j' - i') = j' by omega]
    exact ⟨isIntB_iff.2 hI, rfl⟩

/-- `g = j + 1`: the interval ending at `j` has a value output forever, earlier ones do not -/
def qqCheck (be bo : Nat → Bool) (t0 p j : Nat) : Bool :=
  (List.range j).any (fun i => isIntB bo i j && (perVals be bo t0 p).contains (value be i j)) &&
  (List.range j).all (fun j' => (List.range j').all (fun i =>
    !isIntB bo i j' || !(perVals be bo t0 p).contains (value be i j')))

theorem qq_of_check {be bo : Nat → Bool} {t0 p j : Nat} (hp : 0 < p) (hb : Periodic be t0 p)
    (ho : Periodic bo t0 p) (h : qqCheck be bo t0 p j = true) : QQHaltsAt be bo (j + 1) := by
  unfold qqCheck at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range, List.all_eq_true,
    List.contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨i, hi, hI, hv⟩, hmin⟩ := h
  refine ⟨i, j, isIntB_iff.1 hI, (rep_iff hp hb ho).2 (mem_perVals.1 hv), rfl, ?_⟩
  intro i' j' hI' hr'
  apply Classical.byContradiction; intro hlt
  have := hmin j' (by omega) i' (by have := hI'.lt; omega)
  rcases this with h1 | h1
  · rw [isIntB_iff.2 hI'] at h1; cases h1
  · have := mem_perVals.2 ((rep_iff hp hb ho).1 hr')
    rw [← List.contains_iff_mem] at this
    rw [this] at h1; cases h1

/-- a machine whose transitions are `pre`, then `per` repeated -/
theorem machine_qq_of_check {n : Nat} {M : Machine (n + 1)} {pre per : List (Fin (n + 1) × Bool)}
    (hlab : ∀ k, lab M k = seqv pre per k) (hp : 0 < per.length) (B O : TSet (n + 1)) (j : Nat)
    (h : qqCheck (fun k => evq B (seqv pre per k)) (fun k => evq O (seqv pre per k))
      pre.length per.length j = true) : M.QQHaltsAt B O (j + 1) := by
  have e : ∀ S : TSet (n + 1), ev S M = fun k => evq S (seqv pre per k) := by
    intro S; funext k; rw [ev_eq, hlab]
  have hper : ∀ S : TSet (n + 1), Periodic (fun k => evq S (seqv pre per k)) pre.length per.length :=
    fun S k hk => by simp only; rw [seqv_periodic _ _ _ hk]
  unfold Machine.QQHaltsAt
  rw [e B, e O]
  exact qq_of_check hp (hper B) (hper O) h

/-- the transitions of a translated-cycler certificate: preperiod and period -/
def certLabs {n : Nat} (M : Machine (n + 1)) : Cert → List (Fin (n + 1) × Bool) × List (Fin (n + 1) × Bool)
  | .per t0 p l r kl kr => match wrun M .blank .blank t0 winit with
    | none => ([], [])
    | some (wc, ls0) => match wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => ([], [])
      | some (_, ls) => (ls0, ls)
  | _ => ([], [])

/-- the certificate checks (without the bound) -/
def certOK {n : Nat} (M : Machine (n + 1)) : Cert → Bool
  | .per t0 p l r kl kr => match wrun M .blank .blank t0 winit with
    | none => false
    | some (wc, _) => Fit kl l wc.l && Fit kr r wc.r &&
      match wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => false
      | some (w1, _) => decide (0 < p) && decide (w1.q = wc.q) && Ret kl l w1.l && Ret kr r w1.r
  | _ => false

theorem lab_certLabs {n : Nat} {M : Machine (n + 1)} {c : Cert} (h : certOK M c = true) :
    (∀ k, lab M k = seqv (certLabs M c).1 (certLabs M c).2 k) ∧ 0 < (certLabs M c).2.length := by
  cases c with
  | halt _ => cases h
  | holdout => cases h
  | per t0 p l r kl kr =>
    simp only [certOK] at h
    cases h0 : wrun M .blank .blank t0 winit with
    | none => rw [h0] at h; cases h
    | some x =>
      obtain ⟨wc, ls0⟩ := x
      rw [h0] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hl0, hr0⟩, h⟩ := h
      cases h1 : wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => rw [h1] at h; cases h
      | some y =>
        obtain ⟨w1, ls⟩ := y
        rw [h1] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hp, hq⟩, hl⟩, hr⟩ := h
        have hlen := (wrun_sound (M := M) (X := blank) (Y := blank)
          (by cases kl <;> simp [Adm]) (by cases kr <;> simp [Adm]) p _ w1 ls h1).2.1
        simp only [certLabs, h0, h1]
        exact ⟨lab_eq_seqv (w0 := ⟨wc.q, l, r⟩) hp h0 rfl hl0 hr0 h1 hq hl hr, by omega⟩

/-- `g = j + 1` for a machine with a translated-cycler certificate, by computation -/
theorem qq_of_cert {n : Nat} {M : Machine (n + 1)} {c : Cert} (h : certOK M c = true)
    (B O : TSet (n + 1)) (j : Nat)
    (hq : qqCheck (fun k => evq B (seqv (certLabs M c).1 (certLabs M c).2 k))
      (fun k => evq O (seqv (certLabs M c).1 (certLabs M c).2 k))
      (certLabs M c).1.length (certLabs M c).2.length j = true) : M.QQHaltsAt B O (j + 1) :=
  machine_qq_of_check (lab_certLabs h).1 (lab_certLabs h).2 B O j hq

end Bbbb
