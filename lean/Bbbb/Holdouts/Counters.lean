import Bbbb.Holdouts.Counter

/-!
# The two counters: `0RB0LA_1LA1RB` and `1RB1LA_0LA0RB`

`0RB0LA_1LA1RB` keeps `x` in binary to the right of the head (least significant bit first),
the head on a blank cell in state A; incrementing `x` takes `A0 B1^t B0 A1^t` with
`t = tz x`.  `1RB1LA_0LA0RB` keeps `x` to the left of the head; incrementing takes
`A0 B0 A1^(t+1) A0 B1^(t+1) B0`.
-/

namespace Bbbb

open TM

abbrev A0 : Fin 2 × Bool := (0, false)
abbrev A1 : Fin 2 × Bool := (0, true)
abbrev B0 : Fin 2 × Bool := (1, false)
abbrev B1 : Fin 2 × Bool := (1, true)

/-! ## `0RB0LA_1LA1RB` -/

/-- `0RB0LA_1LA1RB` -/
def cnt1 : Machine 2 := ofCodes2 2 3 7 6

/-- the carry: from the first bit of `x` in state B, back to the cell left of it in state A -/
theorem cnt1_carry : ∀ x (L : Strm), Seg cnt1 ⟨1, L, bin x⟩
    (List.replicate (tz x) B1 ++ [B0] ++ List.replicate (tz x) A1) ⟨0, tl L, L 0 ::: bin (x + 1)⟩ := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro L
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · rw [tz_even hx, bin_even hx]
      refine Seg.congr (Seg.L (M := cnt1) (q := 1) (L := L) (R := false ::: bin (x / 2))
        (w := true) (q' := 0) rfl) rfl ?_ rfl
      rw [bin_odd (x := x + 1) (by omega), show (x + 1) / 2 = x / 2 by omega]; rfl
    · rw [tz_odd hx, bin_odd hx]
      have h1 := Seg.R (M := cnt1) (q := 1) (L := L) (R := true ::: bin (x / 2)) (w := true)
        (q' := 1) rfl
      have h2 := ih (x / 2) (by omega) (true ::: L)
      have h3 := Seg.L (M := cnt1) (q := 0) (L := L) (R := true ::: bin (x / 2 + 1))
        (w := false) (q' := 0) rfl
      refine Seg.congr (h1.trans (h2.trans h3)) rfl ?_ ?_
      · rw [bin_even (x := x + 1) (by omega), show (x + 1) / 2 = x / 2 + 1 by omega]; rfl
      · rw [List.replicate_succ, replicate_succ_right]
        simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
        rfl

def cnt1C (x : Nat) : Cfg (Fin 2) := ⟨0, blank, false ::: bin x⟩

def cnt1W (t : Nat) : List (Fin 2 × Bool) :=
  A0 :: (List.replicate t B1 ++ [B0] ++ List.replicate t A1)

theorem cnt1_round (x : Nat) : Seg cnt1 (cnt1C x) (cnt1W (tz x)) (cnt1C (x + 1)) := by
  have h1 := Seg.R (M := cnt1) (q := 0) (L := blank) (R := false ::: bin x) (w := false)
    (q' := 1) rfl
  have h2 := cnt1_carry x (false ::: blank)
  refine Seg.congr (h1.trans h2) rfl ?_ rfl
  simp only [cnt1C, tl_cons, cons_zero, cons_blank]
  rfl

theorem cnt1_good : Good cnt1 18 := by
  have hpre := counter_prefix (M := cnt1) (C := cnt1C) (W := cnt1W)
    (by show some init = some (cnt1C 0); rw [cnt1C, bin_zero, cons_blank]; rfl)
    cnt1_round (fun t => by simp [cnt1W])
  have h7 : 18 ≤ roundStart 0 (fun x => cnt1W (tz x)) 7 := by
    have l : ∀ t, (cnt1W t).length = 2 * t + 2 := by intro t; simp [cnt1W]; omega
    simp only [roundStart, l]
    have : tz 3 = 2 := by
      rw [tz_odd (x := 3) (by decide), tz_odd (x := 3 / 2) (by decide), tz_even (x := 3 / 2 / 2)
        (by decide)]
    omega
  exact prefix_good (fun N => let ⟨T, hT, h⟩ := hpre N; ⟨T, hT, fun m hm => h m (by omega)⟩)
    (twice_of_twiceB (by decide) (by decide))

/-! ## `1RB1LA_0LA0RB` -/

/-- `1RB1LA_0LA0RB` -/
def cnt2 : Machine 2 := ofCodes2 6 7 3 2

/-- the carry: from the first bit of `x` (to the left of the cells `R`) in state A, to the
right of it in state B -/
theorem cnt2_carry : ∀ x (R : Strm), Seg cnt2 (cfgL' 0 (bin x) R)
    (List.replicate (tz x) A1 ++ [A0] ++ List.replicate (tz x) B1) ⟨1, bin (x + 1), R⟩ := by
  intro x
  induction x using Nat.strongRecOn with
  | ind x ih =>
    intro R
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · rw [tz_even hx, bin_even hx]
      refine Seg.congr (Seg.R (M := cnt2) (q := 0) (L := bin (x / 2)) (R := false ::: R)
        (w := true) (q' := 1) rfl) rfl ?_ rfl
      rw [bin_odd (x := x + 1) (by omega), show (x + 1) / 2 = x / 2 by omega]; rfl
    · rw [tz_odd hx, bin_odd hx]
      have h1 := Seg.L (M := cnt2) (q := 0) (L := bin (x / 2)) (R := true ::: R) (w := true)
        (q' := 0) rfl
      have h2 := ih (x / 2) (by omega) (true ::: R)
      have h3 := Seg.R (M := cnt2) (q := 1) (L := bin (x / 2 + 1)) (R := true ::: R)
        (w := false) (q' := 1) rfl
      refine Seg.congr (h1.trans (h2.trans h3)) rfl ?_ ?_
      · rw [bin_even (x := x + 1) (by omega), show (x + 1) / 2 = x / 2 + 1 by omega]; rfl
      · rw [List.replicate_succ, replicate_succ_right]
        simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
        rfl

def cnt2C (x : Nat) : Cfg (Fin 2) := ⟨0, bin x, blank⟩

def cnt2W (t : Nat) : List (Fin 2 × Bool) :=
  [A0, B0, A1] ++ (List.replicate t A1 ++ [A0] ++ List.replicate t B1) ++ [B1, B0]

theorem cnt2_round (x : Nat) : Seg cnt2 (cnt2C x) (cnt2W (tz x)) (cnt2C (x + 1)) := by
  have h1 := Seg.R (M := cnt2) (q := 0) (L := bin x) (R := blank) (w := true) (q' := 1) rfl
  have h2 := Seg.L (M := cnt2) (q := 1) (L := true ::: bin x) (R := blank) (w := false)
    (q' := 0) rfl
  have h3 := Seg.L (M := cnt2) (q := 0) (L := bin x) (R := true ::: blank) (w := true)
    (q' := 0) rfl
  have h4 := cnt2_carry x (true ::: blank)
  have h5 := Seg.R (M := cnt2) (q := 1) (L := bin (x + 1)) (R := true ::: blank) (w := false)
    (q' := 1) rfl
  have h6 := Seg.L (M := cnt2) (q := 1) (L := false ::: bin (x + 1)) (R := blank) (w := false)
    (q' := 0) rfl
  have e1 : (tl blank : Strm) = blank := rfl
  simp only [e1, tl_cons, cons_zero, cons_blank] at h1 h2 h3 h4 h5 h6
  refine Seg.congr (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))) rfl ?_ ?_
  · simp only [cnt2C, cons_blank]
  · simp only [cnt2W, List.cons_append, List.singleton_append, List.append_assoc, List.nil_append]
    rfl

theorem cnt2_good : Good cnt2 18 := by
  have hpre := counter_prefix (M := cnt2) (C := cnt2C) (W := cnt2W)
    (by show some init = some (cnt2C 0); rw [cnt2C, bin_zero]; rfl)
    cnt2_round (fun t => by simp [cnt2W])
  have h7 : 18 ≤ roundStart 0 (fun x => cnt2W (tz x)) 7 := by
    have l : ∀ t, (cnt2W t).length = 2 * t + 6 := by intro t; simp [cnt2W]; omega
    simp only [roundStart, l]
    omega
  exact prefix_good (fun N => let ⟨T, hT, h⟩ := hpre N; ⟨T, hT, fun m hm => h m (by omega)⟩)
    (twice_of_twiceB (by decide) (by decide))

end Bbbb
