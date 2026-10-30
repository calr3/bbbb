import Bbbb.Decider

/-!
# Machines by codes

A transition of an `(n+1)`-state machine is coded by a number below `4(n+1) + 1`: `0` is
undefined, and `1 + x` writes `x / (2(n+1))`, moves right if `(x / (n+1))` is even and left
otherwise, and goes to state `x % (n+1)` (the order of `tools/gen.py`).  Every machine with one
or two states is given by codes (`exists_codes1`, `exists_codes2`).
-/

namespace Bbbb

open TM

def decTr (n c : Nat) : Option (Bool × Dir × Fin (n + 1)) :=
  if c = 0 then none else
    some (decide ((c - 1) / (2 * (n + 1)) = 1),
      if (c - 1) / (n + 1) % 2 = 0 then Dir.R else Dir.L,
      ⟨(c - 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩)

/-- the 1-state machine with codes `a` (reading 0) and `b` (reading 1) -/
def ofCodes1 (a b : Nat) : Machine 1 := fun _ s => if s then decTr 0 b else decTr 0 a

/-- the 2-state machine with codes `a b` (state A reading 0, 1) and `c d` (state B) -/
def ofCodes2 (a b c d : Nat) : Machine 2 := fun q s =>
  if q.val = 0 then (if s then decTr 1 b else decTr 1 a) else (if s then decTr 1 d else decTr 1 c)

theorem decTr0_surj (t : Option (Bool × Dir × Fin 1)) : ∃ c, c < 5 ∧ decTr 0 c = t := by
  rcases t with _ | ⟨w, d, q, hq⟩
  · exact ⟨0, by decide, rfl⟩
  · match q, hq, w, d with
    | 0, _, false, .L => exact ⟨2, by decide, rfl⟩
    | 0, _, false, .R => exact ⟨1, by decide, rfl⟩
    | 0, _, true, .L => exact ⟨4, by decide, rfl⟩
    | 0, _, true, .R => exact ⟨3, by decide, rfl⟩
    | _ + 1, hq, _, _ => exact absurd hq (by omega)

theorem decTr1_surj (t : Option (Bool × Dir × Fin 2)) : ∃ c, c < 9 ∧ decTr 1 c = t := by
  rcases t with _ | ⟨w, d, q, hq⟩
  · exact ⟨0, by decide, rfl⟩
  · match q, hq, w, d with
    | 0, _, false, .L => exact ⟨3, by decide, rfl⟩
    | 0, _, false, .R => exact ⟨1, by decide, rfl⟩
    | 0, _, true, .L => exact ⟨7, by decide, rfl⟩
    | 0, _, true, .R => exact ⟨5, by decide, rfl⟩
    | 1, _, false, .L => exact ⟨4, by decide, rfl⟩
    | 1, _, false, .R => exact ⟨2, by decide, rfl⟩
    | 1, _, true, .L => exact ⟨8, by decide, rfl⟩
    | 1, _, true, .R => exact ⟨6, by decide, rfl⟩
    | _ + 2, hq, _, _ => exact absurd hq (by omega)

theorem exists_codes1 (M : Machine 1) : ∃ a b, a < 5 ∧ b < 5 ∧ M = ofCodes1 a b := by
  obtain ⟨a, ha, ea⟩ := decTr0_surj (M 0 false)
  obtain ⟨b, hb, eb⟩ := decTr0_surj (M 0 true)
  refine ⟨a, b, ha, hb, ?_⟩
  funext q s
  obtain ⟨q, hq⟩ := q
  match q, hq, s with
  | 0, _, false => simp [ofCodes1, ea]
  | 0, _, true => simp [ofCodes1, eb]
  | _ + 1, hq, _ => exact absurd hq (by omega)

theorem exists_codes2 (M : Machine 2) :
    ∃ a b c d, a < 9 ∧ b < 9 ∧ c < 9 ∧ d < 9 ∧ M = ofCodes2 a b c d := by
  obtain ⟨a, ha, ea⟩ := decTr1_surj (M 0 false)
  obtain ⟨b, hb, eb⟩ := decTr1_surj (M 0 true)
  obtain ⟨c, hc, ec⟩ := decTr1_surj (M 1 false)
  obtain ⟨d, hd, ed⟩ := decTr1_surj (M 1 true)
  refine ⟨a, b, c, d, ha, hb, hc, hd, ?_⟩
  funext q s
  obtain ⟨q, hq⟩ := q
  match q, hq, s with
  | 0, _, false => simp [ofCodes2, ea]
  | 0, _, true => simp [ofCodes2, eb]
  | 1, _, false => simp [ofCodes2, ec]
  | 1, _, true => simp [ofCodes2, ed]
  | _ + 2, hq, _ => exact absurd hq (by omega)

end Bbbb
