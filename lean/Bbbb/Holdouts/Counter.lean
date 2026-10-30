import Bbbb.Holdouts.Seg

/-!
# Binary counters

A counter emits, for each `x = 0, 1, 2, …`, a word `W (tz x)` that depends only on the number
`tz x` of trailing ones of `x`.  Since `tz (x + 8 m) = tz x` for `x < 7`, the words of
`x = 0, …, 6` recur at `x = 8m, …, 8m + 6`: the transitions of the first steps recur forever
(`counter_prefix`).  If every transition occurs twice among the first `K` steps, `g ≤ K` for
every beep set and boop set (`prefix_good`).
-/

namespace Bbbb

open TM

/-- the number of trailing ones -/
def tz (x : Nat) : Nat := if x % 2 = 1 then tz (x / 2) + 1 else 0
decreasing_by omega

theorem tz_even {x : Nat} (h : x % 2 = 0) : tz x = 0 := by
  rw [tz]; simp [h]

theorem tz_odd {x : Nat} (h : x % 2 = 1) : tz x = tz (x / 2) + 1 := by
  rw [tz]; simp [h]

theorem tz_eight {x : Nat} (hx : x < 7) (m : Nat) : tz (x + 8 * m) = tz x := by
  have e : ∀ y, y % 2 = 0 → tz y = 0 := fun y h => tz_even h
  have o : ∀ y, y % 2 = 1 → tz y = tz (y / 2) + 1 := fun y h => tz_odd h
  match x, hx with
  | 0, _ | 2, _ | 4, _ | 6, _ => rw [e _ (by omega), e _ (by omega)]
  | 1, _ =>
    rw [o (1 + 8 * m) (by omega), o 1 (by decide), show (1 + 8 * m) / 2 = 4 * m by omega,
      e (4 * m) (by omega), e (1 / 2) (by decide)]
  | 5, _ =>
    rw [o (5 + 8 * m) (by omega), o 5 (by decide), show (5 + 8 * m) / 2 = 2 + 4 * m by omega,
      e (2 + 4 * m) (by omega), e (5 / 2) (by decide)]
  | 3, _ =>
    rw [o (3 + 8 * m) (by omega), o 3 (by decide), show (3 + 8 * m) / 2 = 1 + 4 * m by omega,
      o (1 + 4 * m) (by omega), o (3 / 2) (by decide), show (1 + 4 * m) / 2 = 2 * m by omega,
      e (2 * m) (by omega), e (3 / 2 / 2) (by decide)]

/-- `x` in binary, least significant bit first -/
def bin (x : Nat) : Strm := fun k => decide (x / 2 ^ k % 2 = 1)

theorem bin_zero : bin 0 = blank := by
  funext k; simp [bin, blank, Nat.zero_div]

theorem bin_cons (x : Nat) : bin x = decide (x % 2 = 1) ::: bin (x / 2) := by
  funext k
  cases k with
  | zero => simp [bin, cons]
  | succ k => simp [bin, cons, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem bin_even {x : Nat} (h : x % 2 = 0) : bin x = false ::: bin (x / 2) := by
  rw [bin_cons]; simp [h]

theorem bin_odd {x : Nat} (h : x % 2 = 1) : bin x = true ::: bin (x / 2) := by
  rw [bin_cons]; simp [h]

/-! ## recurring prefixes -/

/-- If the transitions of the first `K` steps recur forever and each transition occurs twice
among them, then `g ≤ K` whatever the beep and boop sets. -/
theorem prefix_good {M : Machine 2} {K : Nat}
    (hrec : ∀ N, ∃ T, N ≤ T ∧ ∀ m, m < K → lab M (T + m) = lab M m)
    (htwice : ∀ q b, ∃ i j, i < j ∧ j < K ∧ lab M i = some (q, b) ∧ lab M j = some (q, b)) :
    Good M K := by
  intro B O t h
  by_cases hO : ∃ q b, O q b = true
  · obtain ⟨q, b, hqb⟩ := hO
    obtain ⟨i, j, hij, hjK, hi, hj⟩ := htwice q b
    have hbi : ev O M i = true := by rw [ev_eq, hi]; exact hqb
    have hbj : ev O M j = true := by rw [ev_eq, hj]; exact hqb
    obtain ⟨j', hj', hI⟩ := exists_interval hbi j hij hbj
    have hrep : InfinitelyRepeated (ev B M) (ev O M) (value (ev B M) i j') := by
      intro N
      obtain ⟨T, hT, hTm⟩ := hrec N
      obtain ⟨hI', hv⟩ := factor_interval (B := B) (i' := T + i)
        (fun m hm => by
          rw [Nat.add_assoc, hTm (i + m) (by have := hI.lt; omega)]) hI
      exact ⟨_, _, by omega, hI', hv⟩
    have := le_of_rep hI hrep h
    omega
  · exact absurd h (not_of_finite (T := 0) (fun k _ => by
      rw [ev_eq]
      cases e : lab M k with
      | none => rfl
      | some x =>
        obtain ⟨q, b⟩ := x
        cases hq : O q b
        · simp [evq, hq]
        · exact absurd ⟨q, b, hq⟩ hO))

/-- the round of a step before round `n` -/
theorem locate (T0 : Nat) (W : Nat → List (Fin 2 × Bool)) :
    ∀ n k, T0 ≤ k → k < roundStart T0 W n →
      ∃ x, x < n ∧ roundStart T0 W x ≤ k ∧ k < roundStart T0 W (x + 1) := by
  intro n
  induction n with
  | zero => intro k h1 h2; simp only [roundStart] at h2; omega
  | succ n ih =>
    intro k h1 h2
    by_cases hk : k < roundStart T0 W n
    · obtain ⟨x, hx, h3, h4⟩ := ih k h1 hk
      exact ⟨x, by omega, h3, h4⟩
    · exact ⟨n, by omega, by omega, h2⟩

/-- A counter (rounds `W (tz x)` from the start): the transitions of the first 7 rounds recur
forever. -/
theorem counter_prefix {M : Machine 2} {C : Nat → Cfg (Fin 2)} {W : Nat → List (Fin 2 × Bool)}
    (h0 : run M 0 init = some (C 0)) (h : ∀ x, Seg M (C x) (W (tz x)) (C (x + 1)))
    (hW : ∀ t, 0 < (W t).length) :
    ∀ N, ∃ T, N ≤ T ∧ ∀ m, m < roundStart 0 (fun x => W (tz x)) 7 →
      lab M (T + m) = lab M m := by
  have hr := rounds h0 h
  -- the rounds `8m + x`, `x < 7`, start `S (8m)` after round `8m`, as `x` after `0`
  have hS : ∀ m x, x ≤ 7 → roundStart 0 (fun x => W (tz x)) (8 * m + x) =
      roundStart 0 (fun x => W (tz x)) (8 * m) + roundStart 0 (fun x => W (tz x)) x := by
    intro m x hx
    induction x with
    | zero => rfl
    | succ x ih =>
      rw [show 8 * m + (x + 1) = (8 * m + x) + 1 by omega]
      simp only [roundStart]
      rw [ih (by omega), Nat.add_comm (8 * m) x, tz_eight (by omega)]
      omega
  intro N
  refine ⟨roundStart 0 (fun x => W (tz x)) (8 * N), ?_, ?_⟩
  · have := roundStart_ge 0 (fun x => W (tz x)) (fun x => hW _) (8 * N)
    omega
  · intro m hm
    obtain ⟨x, hx, h1, h2⟩ := locate 0 _ 7 m (Nat.zero_le _) hm
    simp only [roundStart] at h2
    have e1 := (hr x).2 (m - roundStart 0 (fun x => W (tz x)) x) (by omega)
    have e2 := (hr (8 * N + x)).2 (m - roundStart 0 (fun x => W (tz x)) x) (by
      rw [Nat.add_comm (8 * N) x, tz_eight hx]; omega)
    rw [show roundStart 0 (fun x => W (tz x)) x + (m - roundStart 0 (fun x => W (tz x)) x) = m
      by omega] at e1
    rw [hS N x (by omega), Nat.add_assoc,
      show roundStart 0 (fun x => W (tz x)) x + (m - roundStart 0 (fun x => W (tz x)) x) = m
      by omega] at e2
    rw [e2, e1, Nat.add_comm (8 * N) x, tz_eight hx]

end Bbbb
