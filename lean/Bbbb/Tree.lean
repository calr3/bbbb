import Bbbb.Exact

/-!
# Trees of partial machines

For more states than two, the machines are not checked one by one: a partial machine (some
transitions undefined) runs until it reaches an undefined transition; the tree then branches on
the choices for that transition.  A leaf is a partial machine whose run never reaches an
undefined transition, with a certificate (`Cert.per`).  Every machine extending a leaf runs as
the leaf does (`lab_ext`), and every machine extends some leaf or halts (`covered_of_check`).
-/

namespace Bbbb

open TM

/-! ## sub-machines -/

section sub
variable {Q : Type} {δ δ' : Q → Bool → Option (Bool × Dir × Q)}
  (hsub : ∀ q b t, δ' q b = some t → δ q b = some t)
include hsub

theorem step_sub {c c' : Cfg Q} (h : step δ' c = some c') : step δ c = some c' := by
  unfold step at h ⊢
  cases ht : δ' c.q (c.R 0) with
  | none => rw [ht] at h; exact absurd h (by simp)
  | some t => rw [hsub _ _ _ ht]; rw [ht] at h; exact h

theorem run_sub : ∀ n (c c' : Cfg Q), run δ' n c = some c' → run δ n c = some c' := by
  intro n
  induction n with
  | zero => intro c c' h; exact h
  | succ n ih =>
    intro c c' h
    simp only [run, Sys.run] at h ⊢
    cases hs : step δ' c with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c1 => rw [step_sub hsub hs]; rw [hs] at h; exact ih c1 c' h

/-- a sub-machine taking a transition at every step takes the same ones as the machine -/
theorem labFrom_sub {c : Cfg Q} {k : Nat} (h : (labFrom δ' c k).isSome) :
    labFrom δ c k = labFrom δ' c k := by
  unfold labFrom at h ⊢
  cases e : run δ' k c with
  | none => rw [e] at h; cases h
  | some d =>
    rw [run_sub hsub k c d e]
    rw [e] at h
    simp only at h ⊢
    cases e2 : δ' d.q (d.R 0) with
    | none => rw [e2] at h; simp at h
    | some t => rw [hsub _ _ _ e2]

end sub

/-! ## partial machines -/

/-- the index of a transition -/
def tIdx {n : Nat} (q : Fin (n + 1)) (b : Bool) : Nat := 2 * q.val + (if b then 1 else 0)

/-- a partial machine: entry `tIdx q b` is `none` (undefined) or the code of the transition -/
abbrev PM := List (Option Nat)

/-- the partial machine as a machine, undefined transitions halting -/
def PM.toM (n : Nat) (P : PM) : Machine (n + 1) := fun q b =>
  match P[tIdx q b]? with
  | some (some c) => decTr n c
  | _ => none

/-- `M` extends `P` -/
def Ext {n : Nat} (M : Machine (n + 1)) (P : PM) : Prop :=
  ∀ q b c, P[tIdx q b]? = some (some c) → M q b = decTr n c

theorem Ext.sub {n : Nat} {M : Machine (n + 1)} {P : PM} (h : Ext M P) :
    ∀ q b t, P.toM n q b = some t → M q b = some t := by
  intro q b t ht
  unfold PM.toM at ht
  cases e : P[tIdx q b]? with
  | none => rw [e] at ht; cases ht
  | some x =>
    cases x with
    | none => rw [e] at ht; cases ht
    | some c => rw [e] at ht; rw [h q b c e]; exact ht

/-- `g` depends only on the transitions taken -/
theorem good_of_lab {n : Nat} {M M' : Machine (n + 1)} {K : Nat} (h : ∀ k, lab M k = lab M' k)
    (hg : Good M' K) : Good M K := by
  intro B O t ht
  have e : ∀ S : TSet (n + 1), ev S M = ev S M' := by
    intro S; funext k; rw [ev_eq, ev_eq, h]
  unfold Machine.QQHaltsAt at ht
  rw [e B, e O] at ht
  exact hg B O t ht

/-! ## leaves -/

/-- a certificate for a leaf: eventually periodic transitions, then the bound -/
def checkLeaf {n : Nat} (M : Machine (n + 1)) (K : Nat) : Cert → Bool
  | .per t0 p l r kl kr => match wrun M .blank .blank t0 winit with
    | none => false
    | some (wc, ls0) => Fit kl l wc.l && Fit kr r wc.r &&
      match wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => false
      | some (w1, ls) => decide (0 < p) && decide (w1.q = wc.q) && Ret kl l w1.l &&
          Ret kr r w1.r && crit ls0 ls K
  | _ => false

theorem checkLeaf_sound {n : Nat} {M : Machine (n + 1)} {K : Nat} {c : Cert}
    (h : checkLeaf M K c = true) : Good M K ∧ ∀ k, (lab M k).isSome := by
  cases c with
  | halt _ => cases h
  | holdout => cases h
  | per t0 p l r kl kr =>
    have hc : checkCert M K (.per t0 p l r kl kr) = true := h
    refine ⟨checkCert_sound hc, ?_⟩
    simp only [checkLeaf] at h
    cases h0 : wrun M .blank .blank t0 winit with
    | none => rw [h0] at h; cases h
    | some x =>
      obtain ⟨wc, ls0⟩ := x
      rw [h0] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hl0, hr0⟩, h⟩ := h
      cases h1 : wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => rw [h1] at h; cases h
      | some y =>
        obtain ⟨w1, ls⟩ := y
        rw [h1] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨hp, hq⟩, hl⟩, hr⟩, _⟩ := h
        have hlab := lab_eq_seqv (w0 := ⟨wc.q, l, r⟩) hp h0 rfl hl0 hr0 h1 hq hl hr
        have hlen := (wrun_sound (M := M) (X := blank) (Y := blank)
          (by cases kl <;> simp [Adm]) (by cases kr <;> simp [Adm]) p _ w1 ls h1).2.1
        intro k
        rw [hlab k]
        unfold seqv
        split
        · simp [List.getElem?_eq_getElem (by omega : k < ls0.length)]
        · simp [List.getElem?_eq_getElem (Nat.mod_lt _ (by omega : 0 < ls.length))]

/-- every machine extending a certified leaf has `g ≤ K` -/
theorem good_of_leaf {n : Nat} {P : PM} {K : Nat} {c : Cert} (h : checkLeaf (P.toM n) K c = true)
    {M : Machine (n + 1)} (hM : Ext M P) : Good M K := by
  obtain ⟨hg, hs⟩ := checkLeaf_sound h
  exact good_of_lab (fun k => labFrom_sub hM.sub (hs k)) hg

/-! ## nodes -/

/-- the transition read after `t` steps of the partial machine, if it halts there -/
def haltIdx {n : Nat} (M : Machine (n + 1)) (t : Nat) : Option Nat :=
  match wrun M .blank .blank t winit with
  | some (wc, _) => match wstep M .blank .blank wc, headR .blank wc.r with
    | .halt, some b => some (tIdx wc.q b)
    | _, _ => none
  | none => none

/-- If the partial machine halts after `t` steps on the undefined transition `i`, a machine
extending it halts there too (so has no `g`) or extends one of the choices for `i`. -/
theorem good_of_node {n : Nat} {P : PM} {K t i : Nat} (hi : haltIdx (P.toM n) t = some i)
    (hu : P[i]? = some none)
    (hk : ∀ c, 1 ≤ c → c < 4 * (n + 1) + 1 → ∀ M : Machine (n + 1), Ext M (P.set i (some c)) →
      Good M K)
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    {M : Machine (n + 1)} (hM : Ext M P) : Good M K := by
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
      -- the run of `M` follows the partial machine for `t` steps
      obtain ⟨hrun, _, _⟩ := wrun_sound (kl := .blank) (kr := .blank) (X := blank) (Y := blank)
        rfl rfl t _ _ _ h0
      rw [winit_den] at hrun
      have hrunM := run_sub hM.sub t _ _ hrun
      have h0' : app wc.r blank 0 = b := headR_sound (kr := .blank) rfl hb
      cases hMb : M wc.q b with
      | none =>
        -- `M` halts at step `t`
        intro B O s hq
        refine absurd hq (not_of_finite (T := t) (fun k hk => ?_))
        apply ev_none
        unfold lab
        rw [show k = t + (k - t) by omega, labFrom_add hrunM]
        cases e : k - t with
        | zero =>
          rw [labFrom_zero]; simp only [Win.den, h0', hMb]; rfl
        | succ j =>
          unfold labFrom
          rw [show j + 1 = 1 + j by omega, run_add]
          simp [run, Sys.run, step, Win.den, h0', hMb]
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
          have : q = wc.q ∧ b' = b := tIdx_inj e
          obtain ⟨rfl, rfl⟩ := this
          rw [hMb, ec]
        · rw [List.getElem?_set_ne (Ne.symm e)] at h'
          exact hM q b' c' h'
where
  tIdx_inj {n : Nat} {q q' : Fin (n + 1)} {b b' : Bool} (h : tIdx q b = tIdx q' b') :
      q = q' ∧ b = b' := by
    unfold tIdx at h
    cases b <;> cases b' <;> simp at h <;> first | omega | exact ⟨Fin.ext (by omega), rfl⟩


/-! ## leaves with a bound for each boop set, and witnesses for each beep set -/

/-- the values of a transition set on the transitions, in index order -/
def bitsOf {n : Nat} (S : TSet (n + 1)) : List Bool :=
  (List.range (2 * (n + 1))).map (fun i => if h : i / 2 < n + 1 then S ⟨i / 2, h⟩ (i % 2 == 1) else false)

def ofBits {n : Nat} (l : List Bool) : TSet (n + 1) := fun q b => l.getD (tIdx q b) false

theorem ofBits_bitsOf {n : Nat} (S : TSet (n + 1)) : ofBits (bitsOf S) = S := by
  funext q b
  obtain ⟨q, hq⟩ := q
  have hi : tIdx (⟨q, hq⟩ : Fin (n + 1)) b < 2 * (n + 1) := by simp only [tIdx, Fin.val_mk]; split <;> omega
  simp only [ofBits, bitsOf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some', Option.getD_some]
  have h1 : tIdx (⟨q, hq⟩ : Fin (n + 1)) b / 2 = q := by simp only [tIdx, Fin.val_mk]; split <;> omega
  have h2 : (tIdx (⟨q, hq⟩ : Fin (n + 1)) b % 2 == 1) = b := by
    simp only [tIdx, Fin.val_mk]; cases b <;> simp <;> omega
  rw [dif_pos (by omega)]
  simp only [h1, h2]

/-- all bit lists of length `m` -/
def allBits : Nat → List (List Bool)
  | 0 => [[]]
  | m + 1 => (allBits m).flatMap (fun l => [false :: l, true :: l])

theorem mem_allBits : ∀ (l : List Bool), l ∈ allBits l.length
  | [] => by simp [allBits]
  | b :: l => by
    simp only [allBits, List.length_cons, List.mem_flatMap, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false]
    exact ⟨l, mem_allBits l, by cases b <;> simp⟩

theorem bitsOf_length {n : Nat} (S : TSet (n + 1)) : (bitsOf S).length = 2 * (n + 1) := by
  simp [bitsOf]

section leafO
variable {n : Nat} (pre per : List (Fin (n + 1) × Bool)) (K : Nat)

/-- the events of a transition set given by bits -/
def evB (l : List Bool) (k : Nat) : Bool := evq (ofBits (n := n) l) (seqv pre per k)

/-- the boop set misses the period -/
def missB (ob : List Bool) : Bool :=
  (List.range per.length).all (fun d => !evB pre per ob (pre.length + d))

/-- two boops after the preperiod, before step `K` -/
def twoB (ob : List Bool) : Bool :=
  (List.range (K - pre.length)).any (fun e1 => (List.range (K - pre.length)).any (fun e2 =>
    decide (e1 < e2) && evB pre per ob (pre.length + e1) && evB pre per ob (pre.length + e2)))

/-- a witness `(ob, bb, i, j, i', j')`: the interval `(i, j)` ends before `K` and has the value
of the interval `(i', j')` in the period -/
def witOK (w : List Bool × List Bool × Nat × Nat × Nat × Nat) : Bool :=
  let (ob, bb, i, j, i', j') := w
  isIntB (evB pre per ob) i j && decide (j < K) && isIntB (evB pre per ob) i' j' &&
    decide (pre.length ≤ i') &&
    decide (value (evB pre per bb) i j = value (evB pre per bb) i' j')

def critO (wit : List (List Bool × List Bool × Nat × Nat × Nat × Nat)) : Bool :=
  (allBits (2 * (n + 1))).all (fun ob => missB pre per ob || twoB pre per K ob ||
    (allBits (2 * (n + 1))).all (fun bb =>
      wit.any (fun w => decide (w.1 = ob) && decide (w.2.1 = bb) && witOK pre per K w)))

end leafO

theorem evB_periodic {n : Nat} (pre per : List (Fin (n + 1) × Bool)) (l : List Bool) :
    Periodic (evB pre per l) pre.length per.length := by
  intro k hk; simp only [evB]; rw [seqv_periodic _ _ _ hk]

theorem seqv_isSome {α : Type} {pre per : List α} (hp : 0 < per.length) (k : Nat) :
    (seqv pre per k).isSome := by
  unfold seqv
  split
  · simp [List.getElem?_eq_getElem (by omega : k < pre.length)]
  · simp [List.getElem?_eq_getElem (Nat.mod_lt _ hp)]

theorem good_of_critO {n : Nat} {M : Machine (n + 1)} {pre per : List (Fin (n + 1) × Bool)} {K : Nat}
    {wit : List (List Bool × List Bool × Nat × Nat × Nat × Nat)}
    (hlab : ∀ k, lab M k = seqv pre per k) (hp : 0 < per.length) (h : critO pre per K wit = true) :
    Good M K := by
  intro B O t hq
  have e : ∀ S : TSet (n + 1), ev S M = evB pre per (bitsOf S) := by
    intro S; funext k; rw [ev_eq, hlab]; simp only [evB, ofBits_bitsOf]
  unfold Machine.QQHaltsAt at hq
  rw [e B, e O] at hq
  have hob := mem_allBits (bitsOf O); rw [bitsOf_length] at hob
  have hbb := mem_allBits (bitsOf B); rw [bitsOf_length] at hbb
  unfold critO at h
  rw [List.all_eq_true] at h
  have h1 := h _ hob
  simp only [Bool.or_eq_true] at h1
  rcases h1 with (h1 | h1) | h1
  · -- the boop set misses the period
    refine absurd hq (not_of_periodic hp (evB_periodic pre per _) (fun k hk1 hk2 => ?_))
    unfold missB at h1
    rw [List.all_eq_true] at h1
    have := h1 (k - pre.length) (List.mem_range.2 (by omega))
    rw [show pre.length + (k - pre.length) = k by omega] at this
    simpa using this
  · -- two boops after the preperiod
    unfold twoB at h1
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨e1, he1, e2, he2, ⟨hlt, b1⟩, b2⟩ := h1
    have := le_of_periodic (T := K - 1) hp (evB_periodic pre per (bitsOf B))
      (evB_periodic pre per (bitsOf O)) (Nat.le_add_right _ e1) (by omega) (by omega) b1 b2 hq
    omega
  · -- a witness for the beep set
    rw [List.all_eq_true] at h1
    have := h1 _ hbb
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨ob, bb, i, j, i', j'⟩, _, ⟨hob', hbb'⟩, hw⟩ := this
    simp only at hob' hbb'
    subst hob' hbb'
    simp only [witOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨⟨⟨⟨hI, hjK⟩, hI'⟩, hi'⟩, hv⟩ := hw
    have hrep := rep_of_periodic hp (evB_periodic pre per (bitsOf B))
      (evB_periodic pre per (bitsOf O)) hi' (isIntB_iff.1 hI')
    rw [← hv] at hrep
    have := le_of_rep (isIntB_iff.1 hI) hrep hq
    omega

/-! ## trees -/

inductive Tree
  /-- a certified leaf -/
  | leaf (c : Cert)
  /-- a leaf with a bound for each boop set, and witnesses for the beep sets -/
  | leafO (c : Cert) (wit : List (List Bool × List Bool × Nat × Nat × Nat × Nat))
  /-- the holdout number `k`, proved separately -/
  | hold (k : Nat)
  /-- the partial machine halts after `t` steps on an undefined transition; the subtrees for
  the codes `1, 2, …` of that transition -/
  | node (t : Nat) (kids : List Tree)

mutual
def checkTree (n K : Nat) (hl : List PM) : PM → Tree → Bool
  | P, .leaf c => checkLeaf (P.toM n) K c
  | P, .leafO c wit => certOK (P.toM n) c &&
      critO (certLabs (P.toM n) c).1 (certLabs (P.toM n) c).2 K wit
  | P, .hold k => decide (hl[k]? = some P)
  | P, .node t kids => match haltIdx (P.toM n) t with
    | some i => decide (P[i]? = some none) && checkKids n K hl P i 1 kids
    | none => false
def checkKids (n K : Nat) (hl : List PM) : PM → Nat → Nat → List Tree → Bool
  | _, _, c, [] => decide (c = 4 * (n + 1) + 1)
  | P, i, c, k :: ks => checkTree n K hl (P.set i (some c)) k && checkKids n K hl P i (c + 1) ks
end

/-- every machine extending `P` has `g ≤ K` -/
def Covered (n K : Nat) (P : PM) : Prop := ∀ M : Machine (n + 1), Ext M P → Good M K

mutual
theorem checkTree_sound {n K : Nat} {hl : List PM}
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    (hh : ∀ (k : Nat) (P : PM), hl[k]? = some P → Covered n K P) :
    ∀ (P : PM) (T : Tree), checkTree n K hl P T = true → Covered n K P
  | P, .leaf c, h => fun _ hM => good_of_leaf (by simpa [checkTree] using h) hM
  | P, .leafO c wit, h => fun M hM => by
    simp only [checkTree, Bool.and_eq_true] at h
    obtain ⟨hlab, hp⟩ := lab_certLabs h.1
    have hg := good_of_critO hlab hp h.2
    exact good_of_lab (fun k => labFrom_sub hM.sub (by
      show (lab (P.toM n) k).isSome; rw [hlab]; exact seqv_isSome hp k)) hg
  | P, .hold k, h => hh k P (by simpa [checkTree] using h)
  | P, .node t kids, h => by
    simp only [checkTree] at h
    cases hi : haltIdx (P.toM n) t with
    | none => rw [hi] at h; cases h
    | some i =>
      rw [hi] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact fun M hM => good_of_node hi h.1
        (fun c h1 h2 => checkKids_sound hsurj hh P i 1 kids h.2 c h1 h2) hsurj hM
theorem checkKids_sound {n K : Nat} {hl : List PM}
    (hsurj : ∀ t : Bool × Dir × Fin (n + 1), ∃ c, c < 4 * (n + 1) + 1 ∧ decTr n c = some t)
    (hh : ∀ (k : Nat) (P : PM), hl[k]? = some P → Covered n K P) :
    ∀ (P : PM) (i c : Nat) (kids : List Tree), checkKids n K hl P i c kids = true →
      ∀ c', c ≤ c' → c' < 4 * (n + 1) + 1 → Covered n K (P.set i (some c'))
  | _, _, c, [], h => fun c' h1 h2 => by
    simp only [checkKids, decide_eq_true_eq] at h; omega
  | P, i, c, k :: ks, h => fun c' h1 h2 => by
    simp only [checkKids, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact checkTree_sound hsurj hh _ k h.1
    · exact checkKids_sound hsurj hh P i (c + 1) ks h.2 c' e h2
end

theorem decTr2_surj (t : Bool × Dir × Fin 3) : ∃ c, c < 13 ∧ decTr 2 c = some t := by
  obtain ⟨w, d, q, hq⟩ := t
  match q, hq, w, d with
  | 0, _, false, .R => exact ⟨1, by decide, rfl⟩
  | 1, _, false, .R => exact ⟨2, by decide, rfl⟩
  | 2, _, false, .R => exact ⟨3, by decide, rfl⟩
  | 0, _, false, .L => exact ⟨4, by decide, rfl⟩
  | 1, _, false, .L => exact ⟨5, by decide, rfl⟩
  | 2, _, false, .L => exact ⟨6, by decide, rfl⟩
  | 0, _, true, .R => exact ⟨7, by decide, rfl⟩
  | 1, _, true, .R => exact ⟨8, by decide, rfl⟩
  | 2, _, true, .R => exact ⟨9, by decide, rfl⟩
  | 0, _, true, .L => exact ⟨10, by decide, rfl⟩
  | 1, _, true, .L => exact ⟨11, by decide, rfl⟩
  | 2, _, true, .L => exact ⟨12, by decide, rfl⟩
  | _ + 3, hq, _, _ => exact absurd hq (by omega)

end Bbbb
