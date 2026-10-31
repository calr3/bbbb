import Bbbb.Holdouts.Bouncers

/-!
# The bouncer `1RB0LB_1LA0RA`

The tape right of the head is `(01)^j`, the head on its first cell in state A, blank to the
left.  A round `(A0 B1)^j A0 B0 (A1 B0)^(j+1)` turns it into `(01)^(j+2)`.  Every boop set
meets one of the repeated blocks: two boops `A0 B1 A0 B1` or `A1 B0 A1 B0` apart recur in
every round from round 1 on (`family_le`).
-/

namespace Bbbb

open TM

/-- `(01)^j`, then `s` -/
def zo : Nat → Strm → Strm
  | 0, s => s
  | j + 1, s => false ::: true ::: zo j s

/-- `(10)^j`, then `s` -/
def oz : Nat → Strm → Strm
  | 0, s => s
  | j + 1, s => true ::: false ::: oz j s

theorem zo_succ' (j : Nat) (s : Strm) : zo (j + 1) s = zo j (false ::: true ::: s) := by
  induction j with
  | zero => rfl
  | succ j ih => show false ::: true ::: zo (j + 1) s = false ::: true ::: zo j _; rw [ih]

theorem oz_succ' (j : Nat) (s : Strm) : oz (j + 1) s = oz j (true ::: false ::: s) := by
  induction j with
  | zero => rfl
  | succ j ih => show true ::: false ::: oz (j + 1) s = true ::: false ::: oz j _; rw [ih]

theorem false_oz (j : Nat) (s : Strm) : false ::: oz j (true ::: s) = zo (j + 1) s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show false ::: true ::: false ::: oz j (true ::: s) = false ::: true ::: zo (j + 1) s
    rw [ih]

/-- `(a b)^j` -/
def pp (a b : Fin 2 × Bool) : Nat → List (Fin 2 × Bool)
  | 0 => []
  | j + 1 => a :: b :: pp a b j

theorem pp_length (a b : Fin 2 × Bool) (j : Nat) : (pp a b j).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [pp, List.length_cons, ih]; omega

theorem pp_succ' (a b : Fin 2 × Bool) (j : Nat) : pp a b (j + 1) = pp a b j ++ [a, b] := by
  induction j with
  | zero => rfl
  | succ j ih => show a :: b :: pp a b (j + 1) = a :: b :: (pp a b j ++ [a, b]); rw [ih]

def bnc4 : Machine 2 := ofCodes2 6 4 7 1

theorem bnc4_sweepR : ∀ j (L s : Strm), Seg bnc4 ⟨0, L, zo j s⟩ (pp A0 B1 j) ⟨0, zo j L, s⟩ := by
  intro j
  induction j with
  | zero => intro L s; exact Seg.nil _ _
  | succ j ih =>
    intro L s
    have h1 := Seg.R (M := bnc4) (q := 0) (L := L) (R := zo (j + 1) s) (w := true) (q' := 1) rfl
    have h2 := Seg.R (M := bnc4) (q := 1) (L := true ::: L) (R := true ::: zo j s) (w := false)
      (q' := 0) rfl
    have h3 := ih (false ::: true ::: L) s
    exact Seg.congr (h1.trans (h2.trans h3)) rfl (by rw [zo_succ']) rfl

theorem bnc4_sweepL : ∀ j (L R : Strm),
    Seg bnc4 ⟨0, zo j L, true ::: R⟩ (pp A1 B0 j) ⟨0, L, true ::: oz j R⟩ := by
  intro j
  induction j with
  | zero => intro L R; exact Seg.nil _ _
  | succ j ih =>
    intro L R
    have h1 := Seg.L (M := bnc4) (q := 0) (L := zo (j + 1) L) (R := true ::: R) (w := false)
      (q' := 1) rfl
    have h2 := Seg.L (M := bnc4) (q := 1) (L := true ::: zo j L) (R := false ::: false ::: R)
      (w := true) (q' := 0) rfl
    have h3 := ih L (true ::: false ::: R)
    exact Seg.congr (h1.trans (h2.trans h3)) rfl (by rw [oz_succ']) rfl

def bnc4W (j : Nat) : List (Fin 2 × Bool) := pp A0 B1 j ++ [A0, B0] ++ pp A1 B0 (j + 1)

theorem bnc4_round (j : Nat) :
    Seg bnc4 ⟨0, blank, zo j blank⟩ (bnc4W j) ⟨0, blank, zo (j + 2) blank⟩ := by
  have h1 := bnc4_sweepR j blank blank
  have h2 := Seg.R (M := bnc4) (q := 0) (L := zo j blank) (R := blank) (w := true) (q' := 1) rfl
  have h3 := Seg.L (M := bnc4) (q := 1) (L := true ::: zo j blank) (R := blank) (w := true)
    (q' := 0) rfl
  have h4 := bnc4_sweepL j blank (true ::: blank)
  have h5 := Seg.L (M := bnc4) (q := 0) (L := blank) (R := true ::: oz j (true ::: blank))
    (w := false) (q' := 1) rfl
  have h6 := Seg.L (M := bnc4) (q := 1) (L := blank) (R := false ::: false ::: oz j (true ::: blank))
    (w := true) (q' := 0) rfl
  simp only [tl_cons, tl_blank, cons_zero] at h2 h3 h5 h6
  refine Seg.congr (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))) rfl ?_ ?_
  · show _ = (⟨0, blank, false ::: true ::: zo (j + 1) blank⟩ : Cfg (Fin 2))
    rw [← false_oz]; rfl
  · simp only [bnc4W, pp_succ', List.append_assoc, List.cons_append, List.singleton_append,
      List.nil_append]
    rfl

/-- An interval inside a factor `F` that occurs at `P (n + 1)` for every `n`: `g ≤ j + 1`. -/
theorem family_le {M : Machine 2} {P : Nat → Nat} {F : List (Fin 2 × Bool)}
    (hP : ∀ n, n ≤ P n) (hF : ∀ n m, m < F.length → lab M (P (n + 1) + m) = F[m]?)
    {B O : TSet 2} {i j : Nat} (hi : P 1 ≤ i) (hj : j < P 1 + F.length)
    (hI : IsInterval (ev O M) i j) {t : Nat} (h : M.QQHaltsAt B O t) : t ≤ j + 1 := by
  refine le_of_rep hI (fun N => ?_) h
  obtain ⟨hI', hv⟩ := factor_interval (B := B) (i' := P (N + 1) + (i - P 1)) (fun m hm => by
    rw [Nat.add_assoc, hF N _ (by have := hI.lt; omega), show i + m = P (0 + 1) + (i - P 1 + m) by
      simp only [Nat.zero_add]; omega, hF 0 _ (by have := hI.lt; omega)]) hI
  exact ⟨_, _, by have := hP (N + 1); omega, hI', hv⟩

/-- two boops at `i` and `i + 2` inside a recurring factor -/
theorem family_le2 {M : Machine 2} {P : Nat → Nat} {F : List (Fin 2 × Bool)}
    (hP : ∀ n, n ≤ P n) (hF : ∀ n m, m < F.length → lab M (P (n + 1) + m) = F[m]?)
    {B O : TSet 2} {d : Nat} (hd : d + 2 < F.length) (h1 : ev O M (P 1 + d) = true)
    (h2 : ev O M (P 1 + d + 2) = true) {t : Nat} (h : M.QQHaltsAt B O t) :
    t ≤ P 1 + F.length := by
  obtain ⟨j', hj', hI⟩ := exists_interval h1 _ (by omega) h2
  have := family_le hP hF (Nat.le_add_right _ _) (by omega) hI h
  omega

def bnc4S : Nat → Nat := roundStart 0 (fun n => bnc4W (2 * n))

def bnc4T (n : Nat) : Nat := bnc4S n + 4 * n + 2

theorem bnc4_good : Good bnc4 18 := by
  have hr : ∀ n, run bnc4 (bnc4S n) init = some ⟨0, blank, zo (2 * n) blank⟩ ∧
      ∀ k, k < (bnc4W (2 * n)).length → lab bnc4 (bnc4S n + k) = (bnc4W (2 * n))[k]? :=
    rounds (M := bnc4) (T0 := 0) (C := fun n => ⟨0, blank, zo (2 * n) blank⟩)
    (W := fun n => bnc4W (2 * n)) rfl (fun n => by
      show Seg bnc4 _ _ ⟨0, blank, zo (2 * (n + 1)) blank⟩
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]; exact bnc4_round (2 * n))
  have hlen : ∀ n, (bnc4W (2 * n)).length = 8 * n + 4 := by
    intro n; simp only [bnc4W, List.length_append, pp_length]; simp; omega
  have hS : ∀ n, n ≤ bnc4S n := fun n => by
    have := roundStart_ge 0 (fun n => bnc4W (2 * n)) (fun n => by rw [hlen]; omega) n
    exact Nat.le_trans (by omega) this
  have hS1 : bnc4S 1 = 4 := by show 0 + (bnc4W (2 * 0)).length = 4; rw [hlen]
  -- the factor `A0 B1 A0 B1` at the start of every round from round 1 on
  have hF1 : ∀ n m, m < [A0, B1, A0, B1].length →
      lab bnc4 (bnc4S (n + 1) + m) = [A0, B1, A0, B1][m]? := by
    intro n m hm
    rw [(hr (n + 1)).2 m (by rw [hlen]; simp at hm; omega)]
    simp only [bnc4W, show 2 * (n + 1) = (2 * n) + 1 + 1 by omega, pp, List.cons_append]
    simp at hm
    match m, hm with
    | 0, _ | 1, _ | 2, _ | 3, _ => simp
  -- the factor `A1 B0 A1 B0` at the start of the left sweep of every round from round 1 on
  have hT : ∀ n, n ≤ bnc4T n := fun n => by have := hS n; simp only [bnc4T]; omega
  have hF2 : ∀ n m, m < [A1, B0, A1, B0].length →
      lab bnc4 (bnc4T (n + 1) + m) = [A1, B0, A1, B0][m]? := by
    intro n m hm
    simp at hm
    simp only [bnc4T]
    rw [show bnc4S (n + 1) + 4 * (n + 1) + 2 + m =
      bnc4S (n + 1) + ((pp A0 B1 (2 * (n + 1)) ++ [A0, B0]).length + m) by simp [pp_length]; omega]
    rw [(hr (n + 1)).2 _ (by rw [hlen]; simp [pp_length]; omega)]
    simp only [bnc4W]
    rw [List.getElem?_append_right (by simp <;> omega)]
    simp only [Nat.add_sub_cancel_left, show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega, pp]
    match m, hm with
    | 0, _ | 1, _ | 2, _ | 3, _ => simp
  have hT1 : bnc4T 1 = 10 := by simp only [bnc4T, hS1]
  intro B O t h
  have evF1 : ∀ m, m < 4 → ev O bnc4 (bnc4S 1 + m) = evq O ([A0, B1, A0, B1][m]?) := by
    intro m hm; rw [ev_eq, show bnc4S 1 = bnc4S (0 + 1) from rfl, hF1 0 m (by simp; omega)]
  have evF2 : ∀ m, m < 4 → ev O bnc4 (bnc4T 1 + m) = evq O ([A1, B0, A1, B0][m]?) := by
    intro m hm; rw [ev_eq, show bnc4T 1 = bnc4T (0 + 1) from rfl, hF2 0 m (by simp; omega)]
  cases eA0 : O 0 false
  · cases eB1 : O 1 true
    · cases eA1 : O 0 true
      · cases eB0 : O 1 false
        · -- no boop at all
          exact absurd h (not_of_finite (T := 0) (fun k _ => by
            rw [ev_eq]
            cases lab bnc4 k with
            | none => rfl
            | some x =>
              obtain ⟨⟨q, hq⟩, b⟩ := x
              match q, hq, b with
              | 0, _, false => exact eA0
              | 0, _, true => exact eA1
              | 1, _, false => exact eB0
              | 1, _, true => exact eB1
              | _ + 2, hq, _ => exact absurd hq (by omega)))
        · have := family_le2 hT hF2 (d := 1) (by decide)
            (by rw [evF2 1 (by decide)]; exact eB0) (by rw [evF2 3 (by decide)]; exact eB0) h
          simp only [hT1, List.length_cons, List.length_nil] at this; omega
      · have := family_le2 hT hF2 (d := 0) (by decide)
          (by rw [evF2 0 (by decide)]; exact eA1) (by rw [evF2 2 (by decide)]; exact eA1) h
        simp only [hT1, List.length_cons, List.length_nil] at this; omega
    · have := family_le2 hS hF1 (d := 1) (by decide)
        (by rw [evF1 1 (by decide)]; exact eB1) (by rw [evF1 3 (by decide)]; exact eB1) h
      simp only [hS1, List.length_cons, List.length_nil] at this; omega
  · have := family_le2 hS hF1 (d := 0) (by decide)
      (by rw [evF1 0 (by decide)]; exact eA0) (by rw [evF1 2 (by decide)]; exact eA0) h
    simp only [hS1, List.length_cons, List.length_nil] at this; omega

end Bbbb
