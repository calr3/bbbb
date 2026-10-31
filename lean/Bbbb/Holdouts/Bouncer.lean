import Bbbb.Holdouts.Counters

/-!
# Bouncers

A bouncer's round `n` (from step `S n`) is `A0 B1^(f n) B0 A1^(g n)` with `f`, `g` strictly
increasing (`BShape`).

* A boop set containing A1 (or B1) has two adjacent boops in every round from the first with
  `g n ≥ 2` (`f n ≥ 2`) on: the value 0 is output forever.
* Otherwise the boops after `S 0` are the A0s, the B0s, or both, in order (`sorted_*`); the
  values of the intervals between them are constant (some value is output forever, first by an
  interval of round 0 or 1) or grow (no value is output forever).
-/

namespace Bbbb

open TM

structure BShape (M : Machine 2) (S f g : Nat → Nat) : Prop where
  hS : ∀ n, S (n + 1) = S n + f n + g n + 2
  hf : ∀ n, f n < f (n + 1)
  hg : ∀ n, g n < g (n + 1)
  hA0 : ∀ n, lab M (S n) = some A0
  hB1 : ∀ n k, k < f n → lab M (S n + 1 + k) = some B1
  hB0 : ∀ n, lab M (S n + 1 + f n) = some B0
  hA1 : ∀ n k, k < g n → lab M (S n + 2 + f n + k) = some A1

/-! ## counting -/

theorem count_succ' (f : Nat → Bool) {a b : Nat} (h : a ≤ b) :
    count f a (b + 1) = count f a b + (if f b then 1 else 0) := by
  unfold count
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range_succ, List.filter_append,
    List.length_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  rw [show a + (b - a) = b by omega]
  by_cases hp : f b <;> simp [hp]

theorem count_add (f : Nat → Bool) {a b c : Nat} (h1 : a ≤ b) (h2 : b ≤ c) :
    count f a c = count f a b + count f b c := by
  induction c, h2 using Nat.le_induction with
  | base => simp [count]
  | succ c hbc ih => rw [count_succ' f (by omega), count_succ' f hbc, ih]; omega

theorem count_const (f : Nat → Bool) {a b : Nat} {c : Bool} (h : ∀ k, a ≤ k → k < b → f k = c) :
    count f a b = if c then b - a else 0 := by
  cases c with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact count_eq_zero h
  | true =>
    simp only [↓reduceIte]
    unfold count
    rw [List.filter_eq_self.2 (fun k hk => by rw [List.mem_range] at hk; exact h _ (by omega) (by omega)),
      List.length_range]

/-! ## sorted boops -/

theorem strictMono_le {p : Nat → Nat} (hp : ∀ m, p m < p (m + 1)) :
    ∀ m m', m ≤ m' → p m ≤ p m' := by
  intro m m' h
  induction m', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ m' _ ih => exact Nat.le_trans ih (Nat.le_of_lt (hp m'))

theorem strictMono_lt {p : Nat → Nat} (hp : ∀ m, p m < p (m + 1)) {m m' : Nat} (h : m < m') :
    p m < p m' :=
  Nat.lt_of_lt_of_le (hp m) (strictMono_le hp _ _ h)

theorem strictMono_ge {p : Nat → Nat} (hp : ∀ m, p m < p (m + 1)) (m : Nat) : p 0 + m ≤ p m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih => have := hp m; omega

theorem strictMono_inj {p : Nat → Nat} (hp : ∀ m, p m < p (m + 1)) {m m' : Nat}
    (h : p m < p m') : m < m' := by
  apply Classical.byContradiction; intro hn
  have := strictMono_le hp m' m (by omega)
  omega

section sorted

variable {be bo : Nat → Bool} {p : Nat → Nat} (hp : ∀ m, p m < p (m + 1))
  (hb : ∀ k, p 0 ≤ k → (bo k = true ↔ ∃ m, k = p m))
include hp hb

theorem sorted_interval (m : Nat) : IsInterval bo (p m) (p (m + 1)) := by
  have h0 := strictMono_ge hp m
  refine ⟨hp m, (hb _ (by omega)).2 ⟨m, rfl⟩, (hb _ (by have := hp m; omega)).2 ⟨m + 1, rfl⟩, ?_⟩
  intro k h1 h2
  cases e : bo k with
  | false => rfl
  | true =>
    obtain ⟨m', rfl⟩ := (hb k (by omega)).1 e
    have := strictMono_inj hp h1
    have := strictMono_inj hp h2
    omega

theorem sorted_of_interval {i j : Nat} (hi : p 0 ≤ i) (hI : IsInterval bo i j) :
    ∃ m, i = p m ∧ j = p (m + 1) := by
  obtain ⟨m, rfl⟩ := (hb i hi).1 hI.left
  obtain ⟨m', rfl⟩ := (hb j (by have := hI.lt; omega)).1 hI.right
  have hmm := strictMono_inj hp hI.lt
  refine ⟨m, rfl, ?_⟩
  rcases Nat.lt_or_ge (m + 1) m' with h | h
  · have := hI.between (p (m + 1)) (hp m) (strictMono_lt hp h)
    rw [(hb _ (by have := strictMono_ge hp (m + 1); omega)).2 ⟨m + 1, rfl⟩] at this
    cases this
  · rw [show m' = m + 1 by omega]

/-- values that grow: nothing is output forever -/
theorem sorted_not_qq (hV : ∀ m, m / 2 ≤ value be (p m) (p (m + 1))) {t : Nat} :
    ¬ QQHaltsAt be bo t := by
  rintro ⟨i0, j0, _, hr, _, _⟩
  obtain ⟨i, j, hi, hI, hv⟩ := hr (p (2 * value be i0 j0 + 2))
  obtain ⟨m, rfl, rfl⟩ := sorted_of_interval hp hb
    (Nat.le_trans (strictMono_le hp 0 _ (Nat.zero_le _)) hi) hI
  have hm : 2 * value be i0 j0 + 2 ≤ m := by
    rcases Nat.lt_or_ge m (2 * value be i0 j0 + 2) with h | h
    · have := strictMono_lt hp h; omega
    · exact h
  have := hV m
  omega

/-- constant values on every other interval: `g ≤ p (r + 1) + 1` -/
theorem sorted_le (r v : Nat) (hV : ∀ m, value be (p (2 * m + r)) (p (2 * m + r + 1)) = v)
    {t : Nat} (h : QQHaltsAt be bo t) : t ≤ p (r + 1) + 1 := by
  have hI := sorted_interval hp hb r
  refine le_of_rep hI ?_ h
  intro N
  refine ⟨_, _, ?_, sorted_interval hp hb (2 * N + r), by rw [hV N, ← hV 0]; simp⟩
  have := strictMono_ge hp (2 * N + r)
  omega

end sorted

theorem bool_or_of_not {a b : Bool} (h : ¬ (a = false ∧ b = false)) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

/-! ## adjacent boops -/

theorem adjacent_rep {be bo : Nat → Bool} (h : ∀ N, ∃ k, N ≤ k ∧ bo k = true ∧ bo (k + 1) = true) :
    InfinitelyRepeated be bo 0 := by
  intro N
  obtain ⟨k, hk, h1, h2⟩ := h N
  exact ⟨k, k + 1, hk, ⟨by omega, h1, h2, fun _ _ _ => by omega⟩, by simp [value, count]⟩

/-! ## bouncers -/

section bouncer

variable {M : Machine 2} {S f g : Nat → Nat} (H : BShape M S f g)
include H

theorem BShape.S_lt (n : Nat) : S n < S (n + 1) := by rw [H.hS]; omega

theorem BShape.f_ge (n : Nat) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => have := H.hf n; omega

theorem BShape.g_ge (n : Nat) : n ≤ g n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => have := H.hg n; omega

theorem BShape.locate : ∀ k, S 0 ≤ k → ∃ n, S n ≤ k ∧ k < S (n + 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨0, Nat.le_refl _, H.S_lt 0⟩
  | succ k _ ih =>
    obtain ⟨n, h1, h2⟩ := ih
    by_cases h : k + 1 < S (n + 1)
    · exact ⟨n, by omega, h⟩
    · exact ⟨n + 1, by omega, by have := H.S_lt (n + 1); omega⟩

/-- the transition at each step from `S 0` on -/
theorem BShape.lab_cases (k : Nat) (hk : S 0 ≤ k) : ∃ n, S n ≤ k ∧ k < S (n + 1) ∧
    ((k = S n ∧ lab M k = some A0) ∨ (S n < k ∧ k < S n + 1 + f n ∧ lab M k = some B1) ∨
      (k = S n + 1 + f n ∧ lab M k = some B0) ∨ (S n + 1 + f n < k ∧ lab M k = some A1)) := by
  obtain ⟨n, h1, h2⟩ := H.locate k hk
  have hs := H.hS n
  refine ⟨n, h1, h2, ?_⟩
  by_cases e0 : k = S n
  · left; subst e0; exact ⟨rfl, H.hA0 n⟩
  by_cases e1 : k < S n + 1 + f n
  · right; left
    have := H.hB1 n (k - (S n + 1)) (by omega)
    rw [show S n + 1 + (k - (S n + 1)) = k by omega] at this
    exact ⟨by omega, e1, this⟩
  by_cases e2 : k = S n + 1 + f n
  · right; right; left; subst e2; exact ⟨rfl, H.hB0 n⟩
  · right; right; right
    have := H.hA1 n (k - (S n + 2 + f n)) (by omega)
    rw [show S n + 2 + f n + (k - (S n + 2 + f n)) = k by omega] at this
    exact ⟨by omega, this⟩

/-- a boop set with A1: `g ≤ S n + f n + 4` for a round with `g n ≥ 2` -/
theorem BShape.le_A1 {B O : TSet 2} (hO : O 0 true = true) {n : Nat} (hn : 2 ≤ g n) {t : Nat}
    (h : M.QQHaltsAt B O t) : t ≤ S n + f n + 4 := by
  have hbo : ∀ m k, k < g m → ev O M (S m + 2 + f m + k) = true := by
    intro m k hk; rw [ev_eq, H.hA1 m k hk]; exact hO
  have hI : IsInterval (ev O M) (S n + 2 + f n) (S n + 2 + f n + 1) :=
    ⟨by omega, by have := hbo n 0 (by omega); simpa using this, hbo n 1 hn, fun _ _ _ => by omega⟩
  have := le_of_rep hI (by
    rw [show value (ev B M) (S n + 2 + f n) (S n + 2 + f n + 1) = 0 by simp [value, count]]
    refine adjacent_rep (fun N => ⟨S (n + N) + 2 + f (n + N), ?_, ?_, hbo _ 1 ?_⟩)
    · have := strictMono_ge H.S_lt (n + N); omega
    · have := hbo (n + N) 0 (by have := strictMono_le H.hg n (n + N) (by omega); omega)
      simpa using this
    · have := strictMono_le H.hg n (n + N) (by omega); omega) h
  omega

/-- a boop set with B1: `g ≤ S n + 3` for a round with `f n ≥ 2` -/
theorem BShape.le_B1 {B O : TSet 2} (hO : O 1 true = true) {n : Nat} (hn : 2 ≤ f n) {t : Nat}
    (h : M.QQHaltsAt B O t) : t ≤ S n + 3 := by
  have hbo : ∀ m k, k < f m → ev O M (S m + 1 + k) = true := by
    intro m k hk; rw [ev_eq, H.hB1 m k hk]; exact hO
  have hI : IsInterval (ev O M) (S n + 1) (S n + 1 + 1) :=
    ⟨by omega, by have := hbo n 0 (by omega); simpa using this, hbo n 1 hn, fun _ _ _ => by omega⟩
  have := le_of_rep hI (by
    rw [show value (ev B M) (S n + 1) (S n + 1 + 1) = 0 by simp [value, count]]
    refine adjacent_rep (fun N => ⟨S (n + N) + 1, ?_, ?_, hbo _ 1 ?_⟩)
    · have := strictMono_ge H.S_lt (n + N); omega
    · have := hbo (n + N) 0 (by have := strictMono_le H.hf n (n + N) (by omega); omega)
      simpa using this
    · have := strictMono_le H.hf n (n + N) (by omega); omega) h
  omega

/-- the beeps of round `n`, block by block -/
theorem BShape.count_B1 (B : TSet 2) (n : Nat) :
    count (ev B M) (S n + 1) (S n + 1 + f n) = if B 1 true then f n else 0 := by
  rw [count_const (c := B 1 true) _ (fun k h1 h2 => by
    have := H.hB1 n (k - (S n + 1)) (by omega)
    rw [show S n + 1 + (k - (S n + 1)) = k by omega] at this
    rw [ev_eq, this]; rfl)]
  split <;> omega

theorem BShape.count_B0 (B : TSet 2) (n : Nat) :
    count (ev B M) (S n + 1 + f n) (S n + 1 + f n + 1) = if B 1 false then 1 else 0 := by
  rw [count_const (c := B 1 false) _ (fun k h1 h2 => by
    rw [show k = S n + 1 + f n by omega, ev_eq, H.hB0 n]; rfl)]
  split <;> omega

theorem BShape.count_A1 (B : TSet 2) (n : Nat) :
    count (ev B M) (S n + 1 + f n + 1) (S (n + 1)) = if B 0 true then g n else 0 := by
  rw [count_const (c := B 0 true) _ (fun k h1 h2 => by
    rw [H.hS] at h2
    have := H.hA1 n (k - (S n + 2 + f n)) (by omega)
    rw [show S n + 2 + f n + (k - (S n + 2 + f n)) = k by omega] at this
    rw [ev_eq, this]; rfl)]
  rw [H.hS]
  split <;> omega

theorem BShape.count_A0 (B : TSet 2) (n : Nat) :
    count (ev B M) (S n) (S n + 1) = if B 0 false then 1 else 0 := by
  rw [count_const (c := B 0 false) _ (fun k h1 h2 => by
    rw [show k = S n by omega, ev_eq, H.hA0 n]; rfl)]
  split <;> omega

/-- a boop set without A1 and B1: `g ≤ S 1 + f 1 + 2`, or no `g` -/
theorem BShape.le_noAB1 {B O : TSet 2} (hA1 : O 0 true = false) (hB1 : O 1 true = false) {t : Nat}
    (h : M.QQHaltsAt B O t) : t ≤ S 1 + f 1 + 2 := by
  have hs := H.hS
  -- the boops from `S 0` on
  have hev : ∀ k, S 0 ≤ k → (ev O M k = true ↔
      ∃ n, (k = S n ∧ O 0 false = true) ∨ (k = S n + 1 + f n ∧ O 1 false = true)) := by
    intro k hk
    obtain ⟨n, h1, h2, hc⟩ := H.lab_cases k hk
    rw [ev_eq]
    constructor
    · intro hb
      rcases hc with ⟨rfl, e⟩ | ⟨_, _, e⟩ | ⟨rfl, e⟩ | ⟨_, e⟩ <;> rw [e] at hb <;>
        simp only [evq] at hb
      · exact ⟨n, Or.inl ⟨rfl, hb⟩⟩
      · rw [hB1] at hb; cases hb
      · exact ⟨n, Or.inr ⟨rfl, hb⟩⟩
      · rw [hA1] at hb; cases hb
    · rintro ⟨n', (⟨rfl, ho⟩ | ⟨rfl, ho⟩)⟩
      · rw [H.hA0]; exact ho
      · rw [H.hB0]; exact ho
  have hb1 : ∀ m, S m + 1 + f m < S (m + 1) := by intro m; rw [hs]; omega
  cases hOA : O 0 false <;> cases hOB : O 1 false
  · -- no boops at all from `S 0` on
    exact absurd h (not_of_finite (T := S 0) (fun k hk => by
      cases e : ev O M k
      · rfl
      · obtain ⟨n, (⟨_, c⟩ | ⟨_, c⟩)⟩ := (hev k hk).1 e
        · rw [hOA] at c; cases c
        · rw [hOB] at c; cases c))
  · -- boops at the B0s
    have hp : ∀ m, S m + 1 + f m < S (m + 1) + 1 + f (m + 1) := by intro m; have := hb1 m; omega
    have hb : ∀ k, S 0 + 1 + f 0 ≤ k → (ev O M k = true ↔ ∃ m, k = S m + 1 + f m) := by
      intro k hk
      rw [hev k (by omega)]
      constructor
      · rintro ⟨n, (⟨_, c⟩ | ⟨rfl, _⟩)⟩
        · rw [hOA] at c; cases c
        · exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨n, Or.inr ⟨rfl, hOB⟩⟩
    have hval : ∀ m, value (ev B M) (S m + 1 + f m) (S (m + 1) + 1 + f (m + 1)) =
        (if B 0 true then g m else 0) + (if B 0 false then 1 else 0) +
          (if B 1 true then f (m + 1) else 0) := by
      intro m
      unfold value
      rw [count_add _ (b := S (m + 1)) (by have := hb1 m; omega) (by omega),
        count_add _ (a := S (m + 1)) (b := S (m + 1) + 1) (by omega) (by omega),
        H.count_A1, H.count_A0, H.count_B1]
      omega
    by_cases hc : B 0 true = false ∧ B 1 true = false
    · have := sorted_le (p := fun m => S m + 1 + f m) hp hb 0
        (if B 0 false then 1 else 0) (fun m => by
          simp only [Nat.add_zero]; rw [hval, hc.1, hc.2]; simp) h
      simp only at this
      simp only [Nat.zero_add] at *
      omega
    · exact absurd h (sorted_not_qq (p := fun m => S m + 1 + f m) hp hb (fun m => by
        simp only; rw [hval]
        rcases bool_or_of_not hc with e | e
        · rw [e]; have := H.g_ge m; simp only [↓reduceIte]; omega
        · rw [e]; have := H.f_ge (m + 1); simp only [↓reduceIte]; omega))
  · -- boops at the A0s
    have hb : ∀ k, S 0 ≤ k → (ev O M k = true ↔ ∃ m, k = S m) := by
      intro k hk
      rw [hev k hk]
      constructor
      · rintro ⟨n, (⟨rfl, _⟩ | ⟨_, c⟩)⟩
        · exact ⟨n, rfl⟩
        · rw [hOB] at c; cases c
      · rintro ⟨n, rfl⟩; exact ⟨n, Or.inl ⟨rfl, hOA⟩⟩
    have hval : ∀ m, value (ev B M) (S m) (S (m + 1)) =
        (if B 1 true then f m else 0) + (if B 1 false then 1 else 0) +
          (if B 0 true then g m else 0) := by
      intro m
      unfold value
      rw [count_add _ (b := S m + 1 + f m) (by omega) (by have := hb1 m; omega),
        count_add _ (a := S m + 1 + f m) (b := S m + 1 + f m + 1) (by omega)
          (by have := hb1 m; omega), H.count_B1, H.count_B0, H.count_A1]
      omega
    by_cases hc : B 0 true = false ∧ B 1 true = false
    · have := sorted_le H.S_lt hb 0 (if B 1 false then 1 else 0) (fun m => by
          simp only [Nat.add_zero]; rw [hval, hc.1, hc.2]; simp) h
      simp only [Nat.zero_add] at *
      omega
    · exact absurd h (sorted_not_qq H.S_lt hb (fun m => by
        rw [hval]
        rcases bool_or_of_not hc with e | e
        · rw [e]; have := H.g_ge m; simp only [↓reduceIte]; omega
        · rw [e]; have := H.f_ge m; simp only [↓reduceIte]; omega))
  · -- boops at the A0s and the B0s, alternately
    let p : Nat → Nat := fun k => if k % 2 = 0 then S (k / 2) else S (k / 2) + 1 + f (k / 2)
    have pe : ∀ m, p (2 * m) = S m := by
      intro m; simp only [p, show 2 * m % 2 = 0 by omega, ↓reduceIte, show 2 * m / 2 = m by omega]
    have po : ∀ m, p (2 * m + 1) = S m + 1 + f m := by
      intro m
      simp only [p, show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
      rfl
    have hp : ∀ k, p k < p (k + 1) := by
      intro k
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [show k = 2 * (k / 2) by omega, pe, po]; omega
      · rw [show k = 2 * (k / 2) + 1 by omega, po, show 2 * (k / 2) + 1 + 1 = 2 * (k / 2 + 1) by omega,
          pe]
        exact hb1 _
    have hb : ∀ k, p 0 ≤ k → (ev O M k = true ↔ ∃ m, k = p m) := by
      intro k hk
      rw [show p 0 = S 0 from pe 0] at hk
      rw [hev k hk]
      constructor
      · rintro ⟨n, (⟨rfl, _⟩ | ⟨rfl, _⟩)⟩
        · exact ⟨2 * n, (pe n).symm⟩
        · exact ⟨2 * n + 1, (po n).symm⟩
      · rintro ⟨m, rfl⟩
        rcases Nat.mod_two_eq_zero_or_one m with hm | hm
        · rw [show m = 2 * (m / 2) by omega, pe]; exact ⟨m / 2, Or.inl ⟨rfl, hOA⟩⟩
        · rw [show m = 2 * (m / 2) + 1 by omega, po]; exact ⟨m / 2, Or.inr ⟨rfl, hOB⟩⟩
    have hv0 : ∀ m, value (ev B M) (p (2 * m)) (p (2 * m + 1)) = if B 1 true then f m else 0 := by
      intro m; rw [pe, po]; exact H.count_B1 B m
    have hv1 : ∀ m, value (ev B M) (p (2 * m + 1)) (p (2 * m + 1 + 1)) =
        if B 0 true then g m else 0 := by
      intro m
      rw [po, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pe]
      exact H.count_A1 B m
    by_cases c1 : B 1 true = false
    · have := sorted_le hp hb 0 0 (fun m => by simp only [Nat.add_zero]; rw [hv0, c1]; rfl) h
      rw [show p (0 + 1) = S 0 + 1 + f 0 from po 0] at this
      have := H.S_lt 0; have := H.hf 0
      simp only [Nat.zero_add] at *
      omega
    by_cases c2 : B 0 true = false
    · have := sorted_le hp hb 1 0 (fun m => by rw [hv1, c2]; rfl) h
      rw [show p (1 + 1) = S 1 from pe 1] at this
      omega
    · exact absurd h (sorted_not_qq hp hb (fun k => by
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk
        · rw [show k = 2 * (k / 2) by omega, hv0]
          simp only [Bool.not_eq_false] at c1; rw [c1]
          have := H.f_ge (k / 2); simp only [↓reduceIte]; omega
        · rw [show k = 2 * (k / 2) + 1 by omega, hv1]
          simp only [Bool.not_eq_false] at c2; rw [c2]
          have := H.g_ge (k / 2); simp only [↓reduceIte]; omega))

end bouncer

end Bbbb
