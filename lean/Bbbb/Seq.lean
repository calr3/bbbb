import Bbbb.Defs

/-!
# Bounds on `g` from the beep and boop sequences

* `le_of_rep`: an interval whose value is output infinitely often bounds `g`.
* `not_of_finite`: finitely many boops, no `g`.
* `exists_interval`: two boops contain an interval starting at the first.
* Eventually periodic sequences: every interval after the preperiod recurs
  (`rep_of_periodic`), so two boops after the preperiod and before `T` give `g ≤ T + 1`
  (`le_of_periodic`).
-/

namespace Bbbb

variable {be bo : Nat → Bool}

theorem le_of_rep {i j t : Nat} (hI : IsInterval bo i j)
    (hr : InfinitelyRepeated be bo (value be i j)) (h : QQHaltsAt be bo t) : t ≤ j + 1 := by
  obtain ⟨_, j0, _, _, rfl, hmin⟩ := h
  have := hmin i j hI hr
  omega

theorem not_of_finite {T t : Nat} (hT : ∀ k, T ≤ k → bo k = false) : ¬ QQHaltsAt be bo t := by
  rintro ⟨i, j, _, hr, _, _⟩
  obtain ⟨i', _, hi', hI', _⟩ := hr T
  have := hT i' hi'
  rw [hI'.left] at this
  cases this

theorem exists_interval {i : Nat} (hi : bo i = true) :
    ∀ j, i < j → bo j = true → ∃ j', j' ≤ j ∧ IsInterval bo i j' := by
  intro j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    intro hij hj
    by_cases h : ∃ k, i < k ∧ k < j ∧ bo k = true
    · obtain ⟨k, h1, h2, h3⟩ := h
      obtain ⟨j', hj', hI⟩ := ih k h2 h1 h3
      exact ⟨j', by omega, hI⟩
    · refine ⟨j, Nat.le_refl _, hij, hi, hj, fun k h1 h2 => ?_⟩
      cases e : bo k
      · rfl
      · exact absurd ⟨k, h1, h2, e⟩ h

/-! ## counting -/

theorem count_congr {f g : Nat → Bool} {a b c : Nat} (h : ∀ k, a ≤ k → k < b → f k = g (k + c)) :
    count f a b = count g (a + c) (b + c) := by
  unfold count
  rw [show b + c - (a + c) = b - a by omega]
  congr 1
  apply List.filter_congr
  intro k hk
  rw [List.mem_range] at hk
  rw [h (a + k) (by omega) (by omega)]
  congr 1
  omega

theorem count_eq_zero {f : Nat → Bool} {a b : Nat} (h : ∀ k, a ≤ k → k < b → f k = false) :
    count f a b = 0 := by
  unfold count
  rw [List.length_eq_zero, List.filter_eq_nil_iff]
  intro k hk
  rw [List.mem_range] at hk
  simp [h (a + k) (by omega) (by omega)]

/-! ## eventually periodic sequences -/

/-- `f` is periodic with period `p` from `t0` on -/
def Periodic (f : Nat → Bool) (t0 p : Nat) : Prop := ∀ n, t0 ≤ n → f (n + p) = f n

theorem Periodic.iter {f : Nat → Bool} {t0 p : Nat} (h : Periodic f t0 p) :
    ∀ m n, t0 ≤ n → f (n + m * p) = f n := by
  intro m
  induction m with
  | zero => intro n _; simp
  | succ m ih =>
    intro n hn
    rw [Nat.succ_mul, ← Nat.add_assoc, h _ (by omega), ih n hn]

/-- an interval after the preperiod recurs one period later -/
theorem interval_shift {t0 p : Nat} (hb : Periodic be t0 p) (ho : Periodic bo t0 p) (m : Nat)
    {i j : Nat} (hi : t0 ≤ i) (hI : IsInterval bo i j) :
    IsInterval bo (i + m * p) (j + m * p) ∧ value be (i + m * p) (j + m * p) = value be i j := by
  refine ⟨⟨by have := hI.lt; omega, ?_, ?_, ?_⟩, ?_⟩
  · rw [ho.iter m i hi]; exact hI.left
  · rw [ho.iter m j (by have := hI.lt; omega)]; exact hI.right
  · intro k h1 h2
    have e := ho.iter m (k - m * p) (by omega)
    rw [show k - m * p + m * p = k by omega] at e
    rw [e]; exact hI.between _ (by omega) (by omega)
  · unfold value
    rw [show i + m * p + 1 = (i + 1) + m * p by omega]
    exact (count_congr (fun k h1 _ => (hb.iter m k (by omega)).symm)).symm

theorem rep_of_periodic {t0 p : Nat} (hp : 0 < p) (hb : Periodic be t0 p) (ho : Periodic bo t0 p)
    {i j : Nat} (hi : t0 ≤ i) (hI : IsInterval bo i j) :
    InfinitelyRepeated be bo (value be i j) := by
  intro N
  obtain ⟨h1, h2⟩ := interval_shift hb ho N hi hI
  refine ⟨_, _, ?_, h1, h2⟩
  have : N ≤ N * p := Nat.le_mul_of_pos_right N hp
  omega

/-- Two boops after the preperiod, the second at step `T` or before: `g ≤ T + 1`. -/
theorem le_of_periodic {t0 p T : Nat} (hp : 0 < p) (hb : Periodic be t0 p)
    (ho : Periodic bo t0 p) {i j : Nat} (hi : t0 ≤ i) (hij : i < j) (hjT : j ≤ T)
    (h1 : bo i = true) (h2 : bo j = true) {t : Nat} (h : QQHaltsAt be bo t) : t ≤ T + 1 := by
  obtain ⟨j', hj', hI⟩ := exists_interval h1 j hij h2
  have := le_of_rep hI (rep_of_periodic hp hb ho hi hI) h
  omega

/-- No boop in one period after the preperiod: no `g`. -/
theorem not_of_periodic {t0 p : Nat} (hp : 0 < p) (ho : Periodic bo t0 p)
    (h : ∀ k, t0 ≤ k → k < t0 + p → bo k = false) {t : Nat} : ¬ QQHaltsAt be bo t := by
  apply not_of_finite (T := t0)
  intro k hk
  have e := ho.iter ((k - t0) / p) (t0 + (k - t0) % p) (by omega)
  rw [show t0 + (k - t0) % p + (k - t0) / p * p = k by
    have := Nat.mod_add_div (k - t0) p; rw [Nat.mul_comm] at this; omega] at e
  rw [e]; exact h _ (by omega) (by have := Nat.mod_lt (k - t0) hp; omega)

end Bbbb
