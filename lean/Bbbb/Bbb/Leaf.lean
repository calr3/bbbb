import Bbbb.Bbb.Defs
import Bbbb.Tree

/-!
# Bounds on the last beep: halting points, eventually periodic runs, sub-machines

`GoodB M K`: every last beep of `M` is at step at most `K`.  A machine that halts after `t`
steps beeps last at step at most `t + 1`; a machine whose transitions are eventually periodic
visits the states of its period forever (no last beep) and the other states only in its
preperiod.  A partial machine that never reaches an undefined transition runs as every machine
extending it.
-/

namespace Bbbb

open TM

/-- every last beep is at step at most `K` -/
def GoodB {n : Nat} (M : Machine (n + 1)) (K : Nat) : Prop :=
  ∀ q s, LastBeep M q s → s ≤ K

/-- the machine never halts -/
def NoHalt {n : Nat} (M : Machine (n + 1)) : Prop := ∀ k, (lab M k).isSome

theorem run_of_lab {n : Nat} {M : Machine (n + 1)} {k : Nat} (h : (lab M k).isSome) :
    ∃ d, run M k init = some d ∧ lab M k = some (d.q, d.R 0) := by
  unfold lab labFrom at *
  cases e : run M k init with
  | none => rw [e] at h; cases h
  | some d =>
    rw [e] at h
    simp only at h ⊢
    refine ⟨d, rfl, ?_⟩
    split at h
    · rw [if_pos (by assumption)]
    · cases h

theorem inState_iff {n : Nat} {M : Machine (n + 1)} (hM : NoHalt M) (q : Fin (n + 1)) (k : Nat) :
    InState M q k ↔ ∃ b, lab M k = some (q, b) := by
  obtain ⟨d, hd, hl⟩ := run_of_lab (hM k)
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [hd] at hc; cases hc
    exact ⟨_, hl⟩
  · rintro ⟨b, hb⟩
    rw [hl] at hb
    cases hb
    exact ⟨d, hd, rfl⟩

/-- a machine extending a partial machine that never halts runs as it does -/
theorem goodB_ext {n : Nat} {P : PM} {K : Nat} (hP : NoHalt (P.toM n)) (hg : GoodB (P.toM n) K)
    {M : Machine (n + 1)} (hM : Ext M P) : GoodB M K := by
  have hrun : ∀ k, run M k init = run (P.toM n) k init := by
    intro k
    obtain ⟨d, hd, _⟩ := run_of_lab (hP k)
    rw [hd]; exact run_sub hM.sub k _ _ hd
  have hs : ∀ q k, InState M q k ↔ InState (P.toM n) q k := by
    intro q k; unfold InState; rw [hrun]
  intro q s ⟨k, hk, hs', hl⟩
  exact hg q s ⟨k, (hs q k).1 hk, hs', fun k' h => by rw [← hs]; exact hl k' h⟩

/-! ## eventually periodic runs -/

/-- the state `q` occurs in the period, or occurs in the preperiod only before step `K` -/
def visOK {n : Nat} (pre per : List (Fin (n + 1) × Bool)) (K q : Nat) : Bool :=
  per.any (fun x => x.1.val == q) ||
    (List.range pre.length).all (fun k => match pre[k]? with
      | some x => x.1.val != q || decide (k + 1 ≤ K)
      | none => true)

def critB {n : Nat} (pre per : List (Fin (n + 1) × Bool)) (K : Nat) : Bool :=
  (List.range (n + 1)).all (visOK pre per K)

theorem noHalt_of_seqv {n : Nat} {M : Machine (n + 1)} {pre per : List (Fin (n + 1) × Bool)}
    (hlab : ∀ k, lab M k = seqv pre per k) (hp : 0 < per.length) : NoHalt M := by
  intro k; rw [hlab]; exact seqv_isSome hp k

theorem goodB_of_critB {n : Nat} {M : Machine (n + 1)} {pre per : List (Fin (n + 1) × Bool)}
    {K : Nat} (hlab : ∀ k, lab M k = seqv pre per k) (hp : 0 < per.length)
    (hc : critB pre per K = true) : GoodB M K := by
  have hM := noHalt_of_seqv hlab hp
  intro q s ⟨k, hk, hs, hlast⟩
  unfold critB at hc
  rw [List.all_eq_true] at hc
  have hv := hc q.val (List.mem_range.2 q.isLt)
  unfold visOK at hv
  by_cases hper : per.any (fun x => x.1.val == q.val) = true
  · -- `q` occurs in the period: a later visit
    rw [List.any_eq_true] at hper
    obtain ⟨x, hx, hxq⟩ := hper
    obtain ⟨d, hd, rfl⟩ := List.getElem_of_mem hx
    let k' := pre.length + d + (k + 1) * per.length
    have hk' : k < k' := by
      have : k + 1 ≤ (k + 1) * per.length := Nat.le_mul_of_pos_right _ hp
      omega
    refine absurd ((inState_iff hM q k').2 ⟨per[d].2, ?_⟩) (hlast k' hk')
    rw [hlab]
    unfold seqv
    rw [if_neg (by omega)]
    have : (k' - pre.length) % per.length = d := by
      rw [show k' - pre.length = d + (k + 1) * per.length by omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hd]
    rw [this, List.getElem?_eq_getElem hd]
    simp only [beq_iff_eq] at hxq
    have e : per[d].1 = q := Fin.ext hxq
    rw [← e]
  · rw [Bool.eq_false_iff.2 hper, Bool.false_or] at hv
    obtain ⟨b, hb⟩ := (inState_iff hM q k).1 hk
    rw [hlab] at hb
    unfold seqv at hb
    split at hb
    · rename_i hlt
      rw [List.all_eq_true] at hv
      have := hv k (List.mem_range.2 hlt)
      rw [hb] at this
      simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq, not_true_eq_false,
        false_or] at this
      omega
    · exfalso
      apply hper
      rw [List.any_eq_true]
      have hlt := Nat.mod_lt (k - pre.length) hp
      rw [List.getElem?_eq_getElem hlt] at hb
      simp only [Option.some.injEq] at hb
      exact ⟨_, List.getElem_mem hlt, by rw [hb]; simp⟩

/-! ## halting points -/

theorem goodB_of_halt {n : Nat} {M : Machine (n + 1)} {K t : Nat} {d : Cfg (Fin (n + 1))}
    (hd : run M t init = some d) (hM : M d.q (d.R 0) = none) (hK : t + 1 ≤ K) : GoodB M K := by
  intro q s ⟨k, ⟨c, hc, _⟩, hs, _⟩
  have hnone : ∀ j, run M (t + 1 + j) init = none := by
    intro j
    rw [run_add, run_add, hd]
    simp [run, Sys.run, step, hM]
  by_cases hk : k ≤ t
  · omega
  · have := hnone (k - t - 1)
    rw [show t + 1 + (k - t - 1) = k by omega, hc] at this
    cases this

/-- If the partial machine halts after `t` steps on the undefined transition `i` (with
`t + 1 ≤ K`), a machine extending it halts there too or extends one of the choices for `i`. -/
theorem goodB_of_node {n : Nat} {P : PM} {K t i : Nat} (hi : haltIdx (P.toM n) t = some i)
    (hu : P[i]? = some none) (hK : t + 1 ≤ K)
    (hk : ∀ c, 1 ≤ c → c < 4 * (n + 1) + 1 → ∀ M : Machine (n + 1), Ext M (P.set i (some c)) →
      GoodB M K)
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    {M : Machine (n + 1)} (hM : Ext M P) : GoodB M K := by
  unfold haltIdx at hi
  cases h0 : wrun (P.toM n) .blank .blank t winit with
  | none => rw [h0] at hi; cases hi
  | some x =>
    obtain ⟨wc, ls⟩ := x
    rw [h0] at hi
    simp only at hi
    obtain ⟨b, hb⟩ := headR_blank wc.r
    rw [hb] at hi
    cases hs : wstep (P.toM n) .blank .blank wc with
    | ok _ => rw [hs] at hi; cases hi
    | stuck => rw [hs] at hi; cases hi
    | halt =>
      rw [hs] at hi
      simp only [Option.some.injEq] at hi
      subst hi
      obtain ⟨hrun, _, _⟩ := wrun_sound (kl := .blank) (kr := .blank) (X := blank) (Y := blank)
        rfl rfl t _ _ _ h0
      rw [winit_den] at hrun
      have hrunM := run_sub hM.sub t _ _ hrun
      have h0' : app wc.r blank 0 = b := headR_sound (kr := .blank) rfl hb
      cases hMb : M wc.q b with
      | none =>
        exact goodB_of_halt hrunM (by simp only [Win.den, h0', hMb]) hK
      | some tr =>
        obtain ⟨c, hc, ec⟩ := hsurj tr
        have hc1 : 1 ≤ c := by
          cases c with
          | zero => simp [decTr] at ec
          | succ _ => omega
        refine hk c hc1 hc M ?_
        intro q b' c' h'
        by_cases e : tIdx q b' = tIdx wc.q b
        · rw [e, List.getElem?_set_self (by
            rcases Nat.lt_or_ge (tIdx wc.q b) P.length with hl | hl
            · exact hl
            · rw [List.getElem?_eq_none hl] at hu; cases hu)] at h'
          simp only [Option.some.injEq] at h'
          subst h'
          have : q = wc.q ∧ b' = b := good_of_node.tIdx_inj e
          obtain ⟨rfl, rfl⟩ := this
          rw [hMb, ec]
        · rw [List.getElem?_set_ne (Ne.symm e)] at h'
          exact hM q b' c' h'

/-! ## periodic leaves -/

/-- a translated-cycler certificate whose states pass `critB` -/
def checkLeafB {n : Nat} (M : Machine (n + 1)) (K : Nat) (c : Cert) : Bool :=
  certOK M c && critB (certLabs M c).1 (certLabs M c).2 K

theorem checkLeafB_sound {n : Nat} {M : Machine (n + 1)} {K : Nat} {c : Cert}
    (h : checkLeafB M K c = true) : GoodB M K ∧ NoHalt M := by
  simp only [checkLeafB, Bool.and_eq_true] at h
  obtain ⟨hlab, hp⟩ := lab_certLabs h.1
  exact ⟨goodB_of_critB hlab hp h.2, noHalt_of_seqv hlab hp⟩

end Bbbb
