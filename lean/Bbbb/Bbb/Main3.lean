import Bbbb.Bbb.Certs.Chunks

/-!
# BBB(3) = 55, given the holdouts

Upper bound: every 3-state machine extends the root of the certified tree (`coverB3`), so every
last beep is at step at most 55, provided the holdouts `holdsB3` are covered.  Lower bound: the
champion `1LB0RB_1RA0LC_1RC1RA` with beep state `B` beeps last at step 55; after 55 steps it stays
in state `C` forever, moving left on a blank tape.
-/

namespace Bbbb

open TM

/-- with eventually periodic transitions, `q` occurs at step `k` of the preperiod, not later in
it, and not in the period -/
def lastOK {n : Nat} (pre per : List (Fin (n + 1) × Bool)) (q k : Nat) : Bool :=
  (pre[k]?.map (·.1.val) == some q) &&
    (List.range pre.length).all (fun j => decide (j ≤ k) || pre[j]?.map (·.1.val) != some q) &&
    per.all (fun x => x.1.val != q)

theorem lastBeep_of_seqv {n : Nat} {M : Machine (n + 1)} {pre per : List (Fin (n + 1) × Bool)}
    (hlab : ∀ k, lab M k = seqv pre per k) (hp : 0 < per.length) (q : Fin (n + 1)) (k : Nat)
    (h : lastOK pre per q.val k = true) : LastBeep M q (k + 1) := by
  have hM := noHalt_of_seqv hlab hp
  simp only [lastOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hk, hlater⟩, hper⟩ := h
  have hkl : k < pre.length := by
    rcases Nat.lt_or_ge k pre.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  refine ⟨k, (inState_iff hM q k).2 ?_, rfl, fun j hj hin => ?_⟩
  · refine ⟨pre[k].2, ?_⟩
    rw [hlab]; unfold seqv; rw [if_pos hkl, List.getElem?_eq_getElem hkl]
    rw [List.getElem?_eq_getElem hkl] at hk
    simp only [Option.map_some', Option.some.injEq] at hk
    rw [show pre[k] = (q, pre[k].2) from Prod.ext (Fin.ext hk) rfl]
  · obtain ⟨b, hb⟩ := (inState_iff hM q j).1 hin
    rw [hlab] at hb
    unfold seqv at hb
    split at hb
    · rename_i hjl
      rcases hlater j hjl with h | h
      · omega
      · exact h (by rw [hb]; rfl)
    · have hlt := Nat.mod_lt (j - pre.length) hp
      rw [List.getElem?_eq_getElem hlt] at hb
      simp only [Option.some.injEq] at hb
      exact hper _ (List.getElem_mem hlt) (by rw [hb])

/-- the champion `1LB0RB_1RA0LC_1RC1RA` -/
def champB3 : Machine 3 := PM.toM 2 [some 11, some 2, some 7, some 6, some 9, some 7]

def champB3Cert : Cert := .per 55 1 [true] [false] .any .blank

set_option maxRecDepth 100000 in
theorem champB3_last : LastBeep champB3 1 55 := by
  have hc : certOK champB3 champB3Cert = true := by decide
  obtain ⟨hlab, hp⟩ := lab_certLabs hc
  exact lastBeep_of_seqv hlab hp 1 54 (by decide)

/-- the holdouts are covered: every machine extending one beeps last at step at most 55 -/
def HoldsB3Covered : Prop := ∀ P ∈ holdsB3, CoveredB 2 55 P

theorem ext_root (M : Machine 3) : Ext M [none, none, none, none, none, none] := by
  intro q b c h
  have : ∀ i : Nat, ([none, none, none, none, none, none] : PM)[i]? ≠ some (some c) := by
    intro i
    rcases i with _ | _ | _ | _ | _ | _ | i <;> simp
  exact absurd h (this _)

/-- `BBB(3) = 55`, given the holdouts -/
theorem bbb3 (hh : HoldsB3Covered) : IsBBB 2 55 :=
  ⟨fun M q s h => coverB3 (coveredB_of_mem hh) M (ext_root M) q s h, champB3, 1, champB3_last⟩

end Bbbb
