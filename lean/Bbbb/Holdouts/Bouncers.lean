import Bbbb.Holdouts.Bouncer

/-!
# The bouncers `1RB1LA_0LA1RB`, `1RB1LA_1LA1RB`, `0RB1LA_1LA1RB`

Each keeps a block of `m` ones to the right of the head, which sits on a blank cell in state A
with blank cells to its left.  A round runs right over the block (`A0 B1^m`), turns at its end
(`B0`) and runs back (`A1^…`), lengthening the block.
-/

namespace Bbbb

open TM

/-- a bouncer round: `A0 B1^a B0 A1^b` -/
def bW (a b : Nat) : List (Fin 2 × Bool) := A0 :: (List.replicate a B1 ++ B0 :: List.replicate b A1)

theorem bW_length (a b : Nat) : (bW a b).length = a + b + 2 := by simp [bW]; omega

theorem bW_A0 (a b : Nat) : (bW a b)[0]? = some A0 := by simp [bW]

theorem bW_B1 {a b k : Nat} (hk : k < a) : (bW a b)[1 + k]? = some B1 := by
  rw [Nat.add_comm, bW, List.getElem?_cons_succ, List.getElem?_append_left (by simp; omega),
    List.getElem?_replicate]
  simp [hk]

theorem bW_B0 (a b : Nat) : (bW a b)[1 + a]? = some B0 := by
  rw [Nat.add_comm, bW, List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp

theorem bW_A1 {a b k : Nat} (hk : k < b) : (bW a b)[2 + a + k]? = some A1 := by
  rw [show 2 + a + k = (a + 1 + k) + 1 by omega, bW, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, show a + 1 + k - a = k + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_replicate]
  simp [hk]

theorem bshape_of_rounds {M : Machine 2} {T0 : Nat} {C : Nat → Cfg (Fin 2)} {f g : Nat → Nat}
    (h0 : run M T0 init = some (C 0)) (h : ∀ n, Seg M (C n) (bW (f n) (g n)) (C (n + 1)))
    (hf : ∀ n, f n < f (n + 1)) (hg : ∀ n, g n < g (n + 1)) :
    BShape M (roundStart T0 (fun n => bW (f n) (g n))) f g := by
  have hr := rounds (W := fun n => bW (f n) (g n)) h0 h
  refine ⟨fun n => ?_, hf, hg, fun n => ?_, fun n k hk => ?_, fun n => ?_, fun n k hk => ?_⟩
  · simp only [roundStart, bW_length]; omega
  · have := (hr n).2 0 (by simp only [bW_length]; omega)
    exact this.trans (bW_A0 _ _)
  · have := (hr n).2 (1 + k) (by simp only [bW_length]; omega)
    rw [bW_B1 hk, ← Nat.add_assoc] at this; exact this
  · have := (hr n).2 (1 + f n) (by simp only [bW_length]; omega)
    rw [bW_B0, ← Nat.add_assoc] at this; exact this
  · have := (hr n).2 (2 + f n + k) (by simp only [bW_length]; omega)
    rw [bW_A1 hk, ← Nat.add_assoc, ← Nat.add_assoc] at this; exact this

theorem bouncer_good {M : Machine 2} {S f g : Nat → Nat} (H : BShape M S f g) {K : Nat}
    (hA1 : ∃ n, 2 ≤ g n ∧ S n + f n + 4 ≤ K) (hB1 : ∃ n, 2 ≤ f n ∧ S n + 3 ≤ K)
    (h3 : S 1 + f 1 + 2 ≤ K) : Good M K := by
  intro B O t h
  cases e1 : O 0 true
  · cases e2 : O 1 true
    · have := H.le_noAB1 e1 e2 h; omega
    · obtain ⟨n, hn, hK⟩ := hB1; have := H.le_B1 e2 hn h; omega
  · obtain ⟨n, hn, hK⟩ := hA1; have := H.le_A1 e1 hn h; omega

/-! ## `1RB1LA_0LA1RB`: the block grows by one -/

def bnc1 : Machine 2 := ofCodes2 6 7 3 6

def bncC (m : Nat) : Cfg (Fin 2) := ⟨0, blank, false ::: ones m blank⟩

theorem bnc1_round (m : Nat) : Seg bnc1 (bncC m) (bW m (m + 1)) (bncC (m + 1)) := by
  have h1 := Seg.R (M := bnc1) (q := 0) (L := blank) (R := false ::: ones m blank) (w := true)
    (q' := 1) rfl
  have h2 := Seg.scanR (M := bnc1) (q := 1) (w := true) rfl m (true ::: blank) blank
  have h3 := Seg.L (M := bnc1) (q := 1) (L := ones (m + 1) blank) (R := blank) (w := false)
    (q' := 0) rfl
  have h4 := Seg.scanL (M := bnc1) (q := 0) (w := true) rfl (m + 1) blank blank
  simp only [tl_cons, ↓reduceIte, ← ones_succ'] at h1 h2
  refine Seg.congr (h1.trans (h2.trans (h3.trans (Seg.congr h4 ?_ rfl rfl)))) rfl rfl ?_
  · show cfgL' 0 (ones (m + 1) blank) blank = _; simp only [cfgL', tl_blank, cons_blank]
  · simp only [bW, List.cons_append, List.singleton_append, List.append_assoc]; rfl

theorem bnc1_good : Good bnc1 18 := by
  have H := bshape_of_rounds (M := bnc1) (T0 := 0) (C := bncC) (f := fun n => n)
    (g := fun n => n + 1) (by show some init = some (bncC 0); simp only [bncC, ones_zero, cons_blank]; rfl)
    (fun n => bnc1_round n) (fun n => by dsimp only; omega) (fun n => by dsimp only; omega)
  refine bouncer_good H ⟨1, by omega, ?_⟩ ⟨2, by omega, ?_⟩ ?_ <;>
    simp only [roundStart, bW_length] <;> omega

/-! ## `1RB1LA_1LA1RB`: the block grows by two -/

def bnc2 : Machine 2 := ofCodes2 6 7 7 6

theorem bnc2_round (m : Nat) : Seg bnc2 (bncC m) (bW m (m + 1)) (bncC (m + 2)) := by
  have h1 := Seg.R (M := bnc2) (q := 0) (L := blank) (R := false ::: ones m blank) (w := true)
    (q' := 1) rfl
  have h2 := Seg.scanR (M := bnc2) (q := 1) (w := true) rfl m (true ::: blank) blank
  have h3 := Seg.L (M := bnc2) (q := 1) (L := ones (m + 1) blank) (R := blank) (w := true)
    (q' := 0) rfl
  have h4 := Seg.scanL (M := bnc2) (q := 0) (w := true) rfl (m + 1) blank (true ::: blank)
  simp only [tl_cons, ↓reduceIte, ← ones_succ'] at h1 h2 h4
  refine Seg.congr (h1.trans (h2.trans (h3.trans (Seg.congr h4 ?_ ?_ rfl)))) rfl rfl ?_
  · rfl
  · simp only [cfgL', bncC, ones_succ' (m + 1)]; rfl
  · simp only [bW, List.cons_append, List.singleton_append, List.append_assoc]; rfl

theorem bnc2_good : Good bnc2 18 := by
  have H := bshape_of_rounds (M := bnc2) (T0 := 0) (C := fun n => bncC (2 * n))
    (f := fun n => 2 * n) (g := fun n => 2 * n + 1) (by show some init = some (bncC 0); simp only [bncC, ones_zero, cons_blank]; rfl)
    (fun n => by
      show Seg bnc2 (bncC (2 * n)) (bW (2 * n) (2 * n + 1)) (bncC (2 * (n + 1)))
      rw [show 2 * (n + 1) = 2 * n + 2 by omega]; exact bnc2_round (2 * n))
    (fun n => by dsimp only; omega) (fun n => by dsimp only; omega)
  refine bouncer_good H ⟨1, by omega, ?_⟩ ⟨1, by omega, ?_⟩ ?_ <;>
    simp only [roundStart, bW_length] <;> omega

/-! ## `0RB1LA_1LA1RB`: the block grows by one, after a prefix -/

def bnc3 : Machine 2 := ofCodes2 2 7 7 6

theorem bnc3_round (m : Nat) : Seg bnc3 (bncC m) (bW m m) (bncC (m + 1)) := by
  have h1 := Seg.R (M := bnc3) (q := 0) (L := blank) (R := false ::: ones m blank) (w := false)
    (q' := 1) rfl
  have h2 := Seg.scanR (M := bnc3) (q := 1) (w := true) rfl m blank blank
  have h3 := Seg.L (M := bnc3) (q := 1) (L := ones m blank) (R := blank) (w := true)
    (q' := 0) rfl
  have h4 := Seg.scanL (M := bnc3) (q := 0) (w := true) rfl m blank (true ::: blank)
  simp only [tl_cons, ↓reduceIte, cons_blank] at h1 h2 h4
  refine Seg.congr (h1.trans (h2.trans (h3.trans (Seg.congr h4 rfl ?_ rfl)))) rfl rfl ?_
  · simp only [cfgL', bncC, ones_succ' m]; rfl
  · simp only [bW, List.cons_append, List.singleton_append, List.append_assoc]; rfl

theorem bnc3_good : Good bnc3 18 := by
  -- the first two steps `A0 B0` reach `bncC 1`
  have h0 : run bnc3 2 init = some (bncC 1) := by
    have h1 := Seg.R (M := bnc3) (q := 0) (L := blank) (R := blank) (w := false) (q' := 1) rfl
    have h2 := Seg.L (M := bnc3) (q := 1) (L := false ::: blank) (R := blank) (w := true)
      (q' := 0) rfl
    exact (h1.trans h2).1.trans (by simp only [bncC, ones_succ, ones_zero]; rfl)
  have H := bshape_of_rounds (M := bnc3) (T0 := 2) (C := fun n => bncC (n + 1))
    (f := fun n => n + 1) (g := fun n => n + 1) h0 (fun n => bnc3_round (n + 1))
    (fun n => by dsimp only; omega) (fun n => by dsimp only; omega)
  refine bouncer_good H ⟨1, by omega, ?_⟩ ⟨1, by omega, ?_⟩ ?_ <;>
    simp only [roundStart, bW_length] <;> omega

end Bbbb
