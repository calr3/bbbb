import Bbbb.Witness

/-!
# Labelled runs and recurring factors

* `Seg M c ls c'`: from `c` the machine takes the transitions `ls` and reaches `c'`.
* `Rounds`: a run cut into rounds `C n → C (n+1)` gives the transitions of every round.
* `factor_interval`: an interval depends only on the transitions from its first boop to its last,
  so a factor of the transition sequence that recurs forever gives a value output forever.
* `prefix_good`: if the transitions of the first `K` steps recur forever and every transition
  occurs twice among them, then `g ≤ K` for every beep set and boop set.
-/

namespace Bbbb

open TM

variable {Q : Type}

/-- From `c` the machine takes the transitions `ls` and reaches `c'`. -/
def Seg (M : Q → Bool → Option (Bool × Dir × Q)) (c : Cfg Q) (ls : List (Q × Bool))
    (c' : Cfg Q) : Prop :=
  run M ls.length c = some c' ∧ ∀ k, k < ls.length → labFrom M c k = ls[k]?

theorem Seg.nil (M : Q → Bool → Option (Bool × Dir × Q)) (c : Cfg Q) : Seg M c [] c :=
  ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

theorem Seg.trans {M : Q → Bool → Option (Bool × Dir × Q)} {c c' c'' : Cfg Q}
    {l1 l2 : List (Q × Bool)} (h1 : Seg M c l1 c') (h2 : Seg M c' l2 c'') :
    Seg M c (l1 ++ l2) c'' := by
  refine ⟨?_, ?_⟩
  · rw [List.length_append, run_add, h1.1]; exact h2.1
  · intro k hk
    rw [List.length_append] at hk
    by_cases hk1 : k < l1.length
    · rw [h1.2 k hk1, List.getElem?_append_left hk1]
    · rw [show k = l1.length + (k - l1.length) by omega, labFrom_add h1.1,
        h2.2 _ (by omega), List.getElem?_append_right (by omega)]
      congr 1; omega

theorem Seg.one {M : Q → Bool → Option (Bool × Dir × Q)} {c c' : Cfg Q}
    (h : step M c = some c') : Seg M c [(c.q, c.R 0)] c' := by
  refine ⟨by simp [run, Sys.run, h], fun k hk => ?_⟩
  simp only [List.length_singleton, Nat.lt_one_iff] at hk
  subst hk
  rw [labFrom_zero]
  cases e : M c.q (c.R 0) with
  | none => simp [step, e] at h
  | some _ => rfl

theorem Seg.R {M : Q → Bool → Option (Bool × Dir × Q)} {q q' : Q} {L R : Strm} {w : Bool}
    (h : M q (R 0) = some (w, .R, q')) : Seg M ⟨q, L, R⟩ [(q, R 0)] ⟨q', w ::: L, tl R⟩ :=
  Seg.one (by simp [step, h])

theorem Seg.L {M : Q → Bool → Option (Bool × Dir × Q)} {q q' : Q} {L R : Strm} {w : Bool}
    (h : M q (R 0) = some (w, .L, q')) :
    Seg M ⟨q, L, R⟩ [(q, R 0)] ⟨q', tl L, L 0 ::: w ::: tl R⟩ :=
  Seg.one (by simp [step, h])

theorem Seg.congr {M : Q → Bool → Option (Bool × Dir × Q)} {c c' d d' : Cfg Q}
    {l l' : List (Q × Bool)} (h : Seg M c l c') (hc : c = d) (hc' : c' = d') (hl : l = l') :
    Seg M d l' d' := by
  subst hc hc' hl; exact h

/-- the run from the start, through a segment -/
theorem Seg.fromInit {n : Nat} {M : Machine (n + 1)} {T : Nat} {c c' : Cfg (Fin (n + 1))}
    {ls : List (Fin (n + 1) × Bool)} (h0 : run M T init = some c) (h : Seg M c ls c') :
    run M (T + ls.length) init = some c' ∧ ∀ k, k < ls.length → lab M (T + k) = ls[k]? := by
  refine ⟨by rw [run_add, h0]; exact h.1, fun k hk => ?_⟩
  unfold lab
  rw [labFrom_add h0]
  exact h.2 k hk

/-! ## scans -/

/-- a right scan over `ones m` in state `q` (reading 1, writing `w`, staying in `q`) -/
theorem Seg.scanR {M : Q → Bool → Option (Bool × Dir × Q)} {q : Q} {w : Bool}
    (h : M q true = some (w, .R, q)) :
    ∀ m (L R : Strm), Seg M ⟨q, L, ones m R⟩ (List.replicate m (q, true))
      ⟨q, (if w then ones m L else zeros m L), R⟩ := by
  intro m
  induction m with
  | zero => intro L R; cases w <;> exact Seg.nil M _
  | succ m ih =>
    intro L R
    have h1 := Seg.R (L := L) (R := ones (m + 1) R) (M := M) (q := q) h
    have h2 := ih (w ::: L) R
    refine Seg.congr (h1.trans h2) rfl ?_ (by rw [List.replicate_succ]; rfl)
    cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [zeros_succ']
    · simp only [↓reduceIte]; rw [ones_succ']

/-- the configuration with the head on `s 0`, the cells `tl s` to its left -/
abbrev cfgL' (q : Q) (s R : Strm) : Cfg Q := ⟨q, tl s, s 0 ::: R⟩

/-- a left scan over `ones m` in state `q` (reading 1, writing `w`, staying in `q`) -/
theorem Seg.scanL {M : Q → Bool → Option (Bool × Dir × Q)} {q : Q} {w : Bool}
    (h : M q true = some (w, .L, q)) :
    ∀ m (s R : Strm), Seg M (cfgL' q (ones m s) R) (List.replicate m (q, true))
      (cfgL' q s (if w then ones m R else zeros m R)) := by
  intro m
  induction m with
  | zero => intro s R; cases w <;> exact Seg.nil M _
  | succ m ih =>
    intro s R
    have h1 := Seg.L (L := tl (ones (m + 1) s)) (R := (ones (m + 1) s) 0 ::: R) (M := M)
      (q := q) h
    have h2 := ih s (w ::: R)
    refine Seg.congr (h1.trans h2) rfl ?_ (by rw [List.replicate_succ]; rfl)
    cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [zeros_succ']
    · simp only [↓reduceIte]; rw [ones_succ']

/-! ## rounds -/

/-- the start of round `n` -/
def roundStart (T0 : Nat) (W : Nat → List (Fin 2 × Bool)) : Nat → Nat
  | 0 => T0
  | n + 1 => roundStart T0 W n + (W n).length

theorem rounds {M : Machine 2} {T0 : Nat} {C : Nat → Cfg (Fin 2)} {W : Nat → List (Fin 2 × Bool)}
    (h0 : run M T0 init = some (C 0)) (h : ∀ n, Seg M (C n) (W n) (C (n + 1))) :
    ∀ n, run M (roundStart T0 W n) init = some (C n) ∧
      ∀ k, k < (W n).length → lab M (roundStart T0 W n + k) = (W n)[k]? := by
  intro n
  induction n with
  | zero => exact ⟨h0, (Seg.fromInit h0 (h 0)).2⟩
  | succ n ih =>
    have := (Seg.fromInit ih.1 (h n)).1
    exact ⟨this, (Seg.fromInit this (h (n + 1))).2⟩

theorem roundStart_ge (T0 : Nat) (W : Nat → List (Fin 2 × Bool)) (hW : ∀ n, 0 < (W n).length) :
    ∀ n, T0 + n ≤ roundStart T0 W n := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => have := hW n; simp only [roundStart]; omega

/-! ## recurring factors -/

/-- An interval depends only on the transitions from its first boop to its last. -/
theorem factor_interval {n : Nat} {M : Machine (n + 1)} {B O : TSet (n + 1)} {i j i' : Nat}
    (hf : ∀ m, m ≤ j - i → lab M (i' + m) = lab M (i + m))
    (hI : IsInterval (ev O M) i j) :
    IsInterval (ev O M) i' (i' + (j - i)) ∧
      value (ev B M) i' (i' + (j - i)) = value (ev B M) i j := by
  have hlt := hI.lt
  have he : ∀ (S : TSet (n + 1)) m, m ≤ j - i → ev S M (i' + m) = ev S M (i + m) := by
    intro S m hm; rw [ev_eq, ev_eq, hf m hm]
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_⟩
  · have := he O 0 (Nat.zero_le _); simp only [Nat.add_zero] at this; rw [this]; exact hI.left
  · rw [he O (j - i) (Nat.le_refl _), show i + (j - i) = j by omega]; exact hI.right
  · intro k h1 h2
    have := he O (k - i') (by omega)
    rw [show i' + (k - i') = k by omega] at this
    rw [this]; exact hI.between _ (by omega) (by omega)
  · unfold value
    rw [count_congr' (a := i + 1) (b := j) (a' := i' + 1) (g := ev B M) (fun k h1 h2 => by
      have := he B (k - i) (by omega)
      rw [show i + (k - i) = k by omega, show i' + (k - i) = k - (i + 1) + (i' + 1) by omega]
        at this
      exact this.symm)]
    congr 1; omega
where
  count_congr' {f g : Nat → Bool} {a b a' : Nat} (h : ∀ k, a ≤ k → k < b → f k = g (k - a + a'))
      : count f a b = count g a' (a' + (b - a)) := by
    unfold count
    rw [show a' + (b - a) - a' = b - a by omega]
    congr 1
    apply List.filter_congr
    intro k hk
    rw [List.mem_range] at hk
    rw [h (a + k) (by omega) (by omega), show a + k - a + a' = a' + k by omega]

end Bbbb

namespace Bbbb

open TM

theorem replicate_succ_right {α : Type} (n : Nat) (a : α) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  rw [show [a] = List.replicate 1 a from rfl, List.append_replicate_replicate]

/-- the transitions of the first `n` steps, by concrete simulation -/
def labs {n : Nat} (M : Machine (n + 1)) (k : Nat) : List (Fin (n + 1) × Bool) :=
  match wrun M .blank .blank k winit with
  | some (_, ls) => ls
  | none => []

theorem lab_labs {n : Nat} {M : Machine (n + 1)} {k : Nat}
    (h : (wrun M .blank .blank k winit).isSome = true) :
    ∀ i, i < k → lab M i = (labs M k)[i]? := by
  cases e : wrun M .blank .blank k winit with
  | none => rw [e] at h; cases h
  | some x =>
    obtain ⟨w, ls⟩ := x
    intro i hi
    have := (wrun_sound (kl := .blank) (kr := .blank) (X := blank) (Y := blank) rfl rfl k _ _ _ e).2.2
      i hi
    rw [winit_den] at this
    unfold labs; rw [e]; exact this

/-- every transition occurs twice among the first `K` entries -/
def twiceB (ls : List (Fin 2 × Bool)) (K : Nat) : Bool :=
  [((0 : Fin 2), false), (0, true), (1, false), (1, true)].all (fun a =>
    (List.range K).any (fun i => (List.range K).any (fun j =>
      decide (i < j) && decide (ls[i]? = some a) && decide (ls[j]? = some a))))

theorem twice_of_twiceB {M : Machine 2} {K : Nat}
    (h : (wrun M .blank .blank K winit).isSome = true) (ht : twiceB (labs M K) K = true) :
    ∀ q b, ∃ i j, i < j ∧ j < K ∧ lab M i = some (q, b) ∧ lab M j = some (q, b) := by
  intro q b
  unfold twiceB at ht
  rw [List.all_eq_true] at ht
  have hq : (q, b) ∈ [((0 : Fin 2), false), (0, true), (1, false), (1, true)] := by
    obtain ⟨q, hq⟩ := q
    match q, hq, b with
    | 0, _, false => simp
    | 0, _, true => simp
    | 1, _, false => simp
    | 1, _, true => simp
    | _ + 2, hq, _ => exact absurd hq (by omega)
  have := ht _ hq
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨i, hi, j, hj, ⟨hij, h1⟩, h2⟩ := this
  exact ⟨i, j, hij, hj, by rw [lab_labs h i hi, h1], by rw [lab_labs h j hj, h2]⟩

end Bbbb
