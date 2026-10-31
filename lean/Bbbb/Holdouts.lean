import Bbbb.Holdouts.Bouncer2
import Bbbb.Core.Mirror
import Bbbb.Certs2

/-!
# The 12 holdouts: 6 machines (`Holdouts/*.lean`) and their mirror images

A mirror image takes the same transitions (`lab_mirror`), so it has the same `g`.
-/

namespace Bbbb

open TM

theorem init_mir {n : Nat} : (init : Cfg (Fin (n + 1))).mir = init := by
  simp only [init, Cfg.mir, tl_blank]
  rw [show blank 0 = false from rfl, cons_blank]

theorem lab_mirror {n : Nat} (M : Machine (n + 1)) (k : Nat) : lab (mirror M) k = lab M k := by
  unfold lab labFrom
  rw [← init_mir, run_mir, init_mir]
  cases run M k init with
  | none => rfl
  | some d =>
    simp only [Option.map, Cfg.mir, cons_zero, mirror]
    cases M d.q (d.R 0) <;> rfl

theorem good_mirror {M : Machine 2} {K : Nat} (h : Good M K) : Good (mirror M) K := by
  intro B O t ht
  have e : ∀ S : TSet 2, ev S (mirror M) = ev S M := by
    intro S; funext k; rw [ev_eq, ev_eq, lab_mirror]
  unfold Machine.QQHaltsAt at ht
  rw [e B, e O] at ht
  exact h B O t ht

theorem mirror_codes {a b c d a' b' c' d' : Nat}
    (h : ∀ q s, mirror (ofCodes2 a b c d) q s = ofCodes2 a' b' c' d' q s) :
    mirror (ofCodes2 a b c d) = ofCodes2 a' b' c' d' := by
  funext q s; exact h q s

theorem good_of_mirror {a b c d a' b' c' d' : Nat} (hg : Good (ofCodes2 a b c d) 18)
    (h : ∀ q s, mirror (ofCodes2 a b c d) q s = ofCodes2 a' b' c' d' q s) :
    Good (ofCodes2 a' b' c' d') 18 := by
  rw [← mirror_codes h]; exact good_mirror hg

theorem mirror_cases {a b c d a' b' c' d' : Nat}
    (h00 : (decTr 1 a).map (fun t => (t.1, t.2.1.flip, t.2.2)) = decTr 1 a')
    (h01 : (decTr 1 b).map (fun t => (t.1, t.2.1.flip, t.2.2)) = decTr 1 b')
    (h10 : (decTr 1 c).map (fun t => (t.1, t.2.1.flip, t.2.2)) = decTr 1 c')
    (h11 : (decTr 1 d).map (fun t => (t.1, t.2.1.flip, t.2.2)) = decTr 1 d') :
    ∀ q s, mirror (ofCodes2 a b c d) q s = ofCodes2 a' b' c' d' q s := by
  intro q s
  obtain ⟨q, hq⟩ := q
  match q, hq, s with
  | 0, _, false => exact h00
  | 0, _, true => exact h01
  | 1, _, false => exact h10
  | 1, _, true => exact h11
  | _ + 2, hq, _ => exact absurd hq (by omega)

theorem holdouts_good : ∀ a b c d, (a, b, c, d) ∈ holdouts2 → Good (ofCodes2 a b c d) 18 := by
  intro a b c d h
  simp only [holdouts2, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact cnt1_good                                                     -- 0RB0LA_1LA1RB
  · exact bnc3_good                                                     -- 0RB1LA_1LA1RB
  · exact good_of_mirror cnt1_good (mirror_cases rfl rfl rfl rfl)       -- 0LB0RA_1RA1LB
  · exact good_of_mirror bnc3_good (mirror_cases rfl rfl rfl rfl)       -- 0LB1RA_1RA1LB
  · exact bnc4_good                                                     -- 1RB0LB_1LA0RA
  · exact cnt2_good                                                     -- 1RB1LA_0LA0RB
  · exact bnc1_good                                                     -- 1RB1LA_0LA1RB
  · exact bnc2_good                                                     -- 1RB1LA_1LA1RB
  · exact good_of_mirror bnc4_good (mirror_cases rfl rfl rfl rfl)       -- 1LB0RB_1RA0LA
  · exact good_of_mirror cnt2_good (mirror_cases rfl rfl rfl rfl)       -- 1LB1RA_0RA0LB
  · exact good_of_mirror bnc1_good (mirror_cases rfl rfl rfl rfl)       -- 1LB1RA_0RA1LB
  · exact good_of_mirror bnc2_good (mirror_cases rfl rfl rfl rfl)       -- 1LB1RA_1RA1LB

end Bbbb
