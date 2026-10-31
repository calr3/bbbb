import Bbbb.Bbb.Abs

/-!
# Recurrence certificates

A certificate is a finite set of abstract nodes closed under `asucc` (so the machine never halts
after the concrete prefix of `t0` steps), together with, for some states `q`, a rank for every
node: a list of components, each a constant or the measure of the left or right tail.  Along
every edge between nodes not in state `q`, the rank decreases lexicographically (`lexDec`).
Since there is no infinite lexicographic descent (`no_descent`), the run visits `q` infinitely
often.  A state without a rank must not occur in any node, so it is visited only in the prefix.
-/

namespace Bbbb

open TM

/-! ## lexicographic descent -/

inductive Comp
  | c (k : Nat)
  | mL
  | mR
deriving DecidableEq, Repr

def Comp.val (tl tr : List Bool) : Comp → Nat
  | .c k => k
  | .mL => mu tl
  | .mR => mu tr

def LexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

def lexDec : List Comp → List Comp → Eff → Eff → Bool
  | x :: xs, y :: ys, eL, eR => match x, y with
    | .c a, .c b => decide (b < a) || (decide (a = b) && lexDec xs ys eL eR)
    | .mL, .mL => match eL with
      | .dec => true
      | .le => lexDec xs ys eL eR
      | .any => false
    | .mR, .mR => match eR with
      | .dec => true
      | .le => lexDec xs ys eL eR
      | .any => false
    | _, _ => false
  | _, _, _, _ => false

theorem lexDec_sound {tl tr tl' tr' : List Bool} {eL eR : Eff} (hL : eL.ok tl tl')
    (hR : eR.ok tr tr') : ∀ (xs ys : List Comp), lexDec xs ys eL eR = true →
      LexLt (ys.map (Comp.val tl' tr')) (xs.map (Comp.val tl tr))
  | [], _, h => by simp [lexDec] at h
  | _ :: _, [], h => by simp [lexDec] at h
  | x :: xs, y :: ys, h => by
    have ih := lexDec_sound hL hR xs ys
    simp only [List.map_cons, LexLt]
    cases x <;> cases y <;> simp only [lexDec, Bool.false_eq_true] at h
    · simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
      simp only [Comp.val]
      rcases h with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, ih h⟩
    · simp only [Comp.val]
      cases eL <;> simp only [Eff.ok, Bool.false_eq_true] at h hL
      · exact Or.inl hL
      · rcases Nat.lt_or_eq_of_le hL with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h', ih h⟩
    · simp only [Comp.val]
      cases eR <;> simp only [Eff.ok, Bool.false_eq_true] at h hR
      · exact Or.inl hR
      · rcases Nat.lt_or_eq_of_le hR with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨h', ih h⟩

theorem le_zero_of_mono {h : Nat → Nat} (hm : ∀ m, h (m + 1) ≤ h m) : ∀ m, h m ≤ h 0
  | 0 => Nat.le_refl _
  | m + 1 => Nat.le_trans (hm m) (le_zero_of_mono hm m)

theorem eventually_const : ∀ (v : Nat) (h : Nat → Nat), h 0 = v → (∀ m, h (m + 1) ≤ h m) →
    ∃ N, ∀ m, N ≤ m → h m = h N := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro h h0 hm
    by_cases hall : ∀ m, h m = h 0
    · exact ⟨0, fun m _ => hall m⟩
    · have ⟨m, hne⟩ : ∃ m, h m ≠ h 0 := Classical.byContradiction fun hc =>
        hall fun m => Classical.byContradiction fun e => hc ⟨m, e⟩
      have hlt : h m < v := by have := le_zero_of_mono hm m; omega
      obtain ⟨N, hN⟩ := ih (h m) hlt (fun j => h (m + j)) rfl (fun j => hm (m + j))
      refine ⟨m + N, fun k hk => ?_⟩
      have := hN (k - m) (by omega)
      rwa [show m + (k - m) = k by omega] at this

theorem no_descent : ∀ (L : Nat) (f : Nat → List Nat), (∀ m, (f m).length = L) →
    ¬ ∀ m, LexLt (f (m + 1)) (f m) := by
  intro L
  induction L with
  | zero =>
    intro f hl hd
    have := hd 0
    rw [List.length_eq_zero.1 (hl 0)] at this
    cases e : f 1 <;> rw [e] at this <;> exact this
  | succ L ih =>
    intro f hl hd
    have hf : ∀ m, f m = (f m).headD 0 :: (f m).tail := by
      intro m
      cases e : f m with
      | nil => have := hl m; rw [e] at this; cases this
      | cons a as => rfl
    have hstep : ∀ m, (f (m + 1)).headD 0 < (f m).headD 0 ∨
        ((f (m + 1)).headD 0 = (f m).headD 0 ∧ LexLt (f (m + 1)).tail (f m).tail) := by
      intro m
      have := hd m
      rw [hf m, hf (m + 1)] at this
      exact this
    obtain ⟨N, hN⟩ := eventually_const _ (fun m => (f m).headD 0) rfl
      (fun m => by simp only; rcases hstep m with h | h <;> omega)
    refine ih (fun j => (f (N + j)).tail) (fun j => by simp [hl]) (fun j => ?_)
    rcases hstep (N + j) with h | h
    · have e1 := hN (N + j + 1) (by omega)
      have e2 := hN (N + j) (by omega)
      simp only at e1 e2; omega
    · show LexLt (f (N + (j + 1))).tail (f (N + j)).tail
      rw [show N + (j + 1) = N + j + 1 by omega]; exact h.2

/-! ## certificates -/

structure ACert (n : Nat) where
  t0 : Nat
  R : Nat
  spL : SP
  spR : SP
  /-- the nodes, each with the indices of its successors (in the order of `asucc`) -/
  nodes : List (ANode n × List Nat)
  /-- for some states, a rank for each node -/
  ranks : List (Nat × List (List Comp))

variable {n : Nat}

/-- the successors of node `i` are listed and the ranks decrease along its edges -/
def nodeOK (M : Machine (n + 1)) (c : ACert n) (i : Nat) : Bool :=
  match c.nodes[i]? with
  | none => false
  | some (v, succ) => match asucc M c.R c.spL c.spR v with
    | none => false
    | some es => es.length == succ.length && (es.zip succ).all fun p => match c.nodes[p.2]? with
      | none => false
      | some (v', _) => decide (v' = p.1.2.2) && c.ranks.all fun x =>
        decide (v.q.val = x.1) || decide (v'.q.val = x.1) ||
          match x.2[i]?, x.2[p.2]? with
          | some a, some b => lexDec a b p.1.1 p.1.2.1
          | _, _ => false

/-- every rank of the list has the same length -/
def rankLen (c : ACert n) (rk : List (List Comp)) : Bool :=
  rk.length == c.nodes.length && rk.all fun a => a.length == (rk.headD []).length

/-- the state `q` occurs in no node, and in the prefix only before step `K` -/
def absentOK (c : ACert n) (ls0 : List (Fin (n + 1) × Bool)) (K q : Nat) : Bool :=
  c.nodes.all (fun p => p.1.q.val != q) &&
    (List.range ls0.length).all fun k => match ls0[k]? with
      | some x => x.1.val != q || decide (k + 1 ≤ K)
      | none => true

def checkACert (M : Machine (n + 1)) (K : Nat) (c : ACert n) : Bool :=
  match wrun M .blank .blank c.t0 winit with
  | none => false
  | some (wc, ls0) =>
    (c.nodes[0]?.map (·.1) == some ⟨wc.q, wc.l, wc.r, .blank, .blank⟩) &&
    (List.range c.nodes.length).all (nodeOK M c) &&
    c.ranks.all (fun x => rankLen c x.2) &&
    (List.range (n + 1)).all fun q => c.ranks.any (·.1 == q) || absentOK c ls0 K q

/-! ## soundness -/

section sound
variable {M : Machine (n + 1)} {c : ACert n}

/-- a node index with tails of its kinds -/
def AS (c : ACert n) (x : Nat × List Bool × List Bool) : Prop :=
  ∃ v succ, c.nodes[x.1]? = some (v, succ) ∧ v.kl.mem c.spL x.2.1 ∧ v.kr.mem c.spR x.2.2

/-- the node of an index -/
def nodeAt (c : ACert n) (i : Nat) : Option (ANode n) := c.nodes[i]?.map (·.1)

/-- the rank values -/
def rval (rk : List (List Comp)) (x : Nat × List Bool × List Bool) : List Nat :=
  (rk[x.1]?.getD []).map (Comp.val x.2.1 x.2.2)

/-- `y` is a successor of `x`: one step, and the ranks decrease off their states -/
def ARel (M : Machine (n + 1)) (c : ACert n) (x y : Nat × List Bool × List Bool) : Prop :=
  AS c y ∧ ∃ v v', nodeAt c x.1 = some v ∧ nodeAt c y.1 = some v' ∧
    step M (v.den x.2.1 x.2.2) = some (v'.den y.2.1 y.2.2) ∧
    ∀ r ∈ c.ranks, v.q.val ≠ r.1 → v'.q.val ≠ r.1 → LexLt (rval r.2 y) (rval r.2 x)

theorem adv_of_nodeOK (hok : ∀ i, i < c.nodes.length → nodeOK M c i = true)
    {x : Nat × List Bool × List Bool} (hx : AS c x) : ∃ y, ARel M c x y := by
  obtain ⟨v, succ, hv, hl, hr⟩ := hx
  have hi : x.1 < c.nodes.length := by
    rcases Nat.lt_or_ge x.1 c.nodes.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  have h := hok x.1 hi
  unfold nodeOK at h
  rw [hv] at h
  simp only at h
  cases ha : asucc M c.R c.spL c.spR v with
  | none => rw [ha] at h; cases h
  | some es =>
    rw [ha] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨hlen, hall⟩ := h
    obtain ⟨e, he, tl', tr', hst, hkl, hkr, hoL, hoR⟩ := asucc_sound ha hl hr
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem he
    have hidx' : idx < succ.length := hlen ▸ hidx
    have hz : (es[idx], succ[idx]) ∈ es.zip succ := by
      rw [List.mem_iff_getElem]
      exact ⟨idx, by simp only [List.length_zip]; omega, by simp⟩
    have hp := hall _ hz
    simp only at hp
    cases hj : c.nodes[succ[idx]]? with
    | none => rw [hj] at hp; cases hp
    | some y =>
      obtain ⟨v', succ'⟩ := y
      rw [hj] at hp
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hp
      obtain ⟨rfl, hrk⟩ := hp
      refine ⟨(succ[idx], tl', tr'), ⟨_, _, hj, hkl, hkr⟩, v, es[idx].2.2,
        by simp [nodeAt, hv], by simp [nodeAt, hj], hst, ?_⟩
      intro r hr hq hq'
      have := hrk r hr
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with (h | h) | h
      · exact absurd h hq
      · exact absurd h hq'
      · unfold rval
        cases h1 : r.2[x.1]? with
        | none => rw [h1] at h; cases h
        | some a =>
          cases h2 : r.2[succ[idx]]? with
          | none => rw [h1, h2] at h; cases h
          | some b =>
            rw [h1, h2] at h
            simpa using lexDec_sound hoL hoR a b h

theorem lab_isSome_of_run {k : Nat} {d : Cfg (Fin (n + 1))} (h : run M (k + 1) init = some d) :
    (lab M k).isSome := by
  unfold lab labFrom
  rw [run_add] at h
  cases e : run M k init with
  | none => rw [e] at h; cases h
  | some d0 =>
    rw [e] at h
    have h' : run M 1 d0 = some d := h
    simp only
    cases hs : M d0.q (d0.R 0) with
    | none =>
      have : step M d0 = none := by simp [step, hs]
      simp [run, Sys.run, this] at h'
    | some _ => simp

open Classical in
theorem checkACert_sound {K : Nat} (h : checkACert M K c = true) : GoodB M K ∧ NoHalt M := by
  unfold checkACert at h
  cases h0 : wrun M .blank .blank c.t0 winit with
  | none => rw [h0] at h; cases h
  | some x0 =>
    obtain ⟨wc, ls0⟩ := x0
    rw [h0] at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      List.any_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hstart, hok⟩, hlen⟩, hq⟩ := h
    obtain ⟨hrun0, hlen0, hlab0⟩ := wrun_sound (kl := .blank) (kr := .blank) (X := blank)
      (Y := blank) rfl rfl c.t0 _ _ _ h0
    rw [winit_den] at hrun0 hlab0
    -- the start
    have hs0 : AS c (0, [], []) := by
      cases e : c.nodes[0]? with
      | none => rw [e] at hstart; cases hstart
      | some p =>
        obtain ⟨v, succ⟩ := p
        rw [e] at hstart
        simp only [Option.map_some', Option.some.injEq] at hstart
        subst hstart
        exact ⟨_, succ, e, rfl, rfl⟩
    have hc0 : nodeAt c 0 = some ⟨wc.q, wc.l, wc.r, .blank, .blank⟩ := by
      simpa [nodeAt] using hstart
    -- the path
    let nxt : Nat × List Bool × List Bool → Nat × List Bool × List Bool := fun x =>
      if hx : AS c x then Classical.choose (adv_of_nodeOK hok hx) else x
    let sq : Nat → Nat × List Bool × List Bool := fun m => Nat.rec (0, [], []) (fun _ x => nxt x) m
    have hsq : ∀ m, sq (m + 1) = nxt (sq m) := fun m => rfl
    have hinv : ∀ m, AS c (sq m) ∧ ∃ v, nodeAt c (sq m).1 = some v ∧
        run M (c.t0 + m) init = some (v.den (sq m).2.1 (sq m).2.2) := by
      intro m
      induction m with
      | zero =>
        refine ⟨hs0, _, hc0, ?_⟩
        show run M c.t0 init = some (ANode.den ⟨wc.q, wc.l, wc.r, .blank, .blank⟩ [] [])
        rw [hrun0]; simp [Win.den, ANode.den]
      | succ m ih =>
        obtain ⟨hA, v, hv, hr⟩ := ih
        have hrel : ARel M c (sq m) (sq (m + 1)) := by
          rw [hsq]; simp only [nxt, dif_pos hA]; exact Classical.choose_spec (adv_of_nodeOK hok hA)
        obtain ⟨hA', v1, v', hv1, hv', hst, _⟩ := hrel
        rw [hv] at hv1; cases hv1
        refine ⟨hA', v', hv', ?_⟩
        rw [← Nat.add_assoc, run_add, hr]
        show run M 1 _ = _
        simp only [run, Sys.run, hst]
    have hrel : ∀ m, ARel M c (sq m) (sq (m + 1)) := by
      intro m
      rw [hsq]; simp only [nxt, dif_pos (hinv m).1]
      exact Classical.choose_spec (adv_of_nodeOK hok (hinv m).1)
    -- never halts
    have hnh : NoHalt M := by
      intro k
      by_cases hk : k < c.t0
      · rw [lab, hlab0 k hk, List.getElem?_eq_getElem (by omega)]; rfl
      · obtain ⟨_, v, _, hr⟩ := hinv (k + 1 - c.t0)
        rw [show c.t0 + (k + 1 - c.t0) = k + 1 by omega] at hr
        exact lab_isSome_of_run hr
    refine ⟨?_, hnh⟩
    -- the state after `t0 + m` steps is that of the node
    have hstate : ∀ m q, InState M q (c.t0 + m) → ∃ v, nodeAt c (sq m).1 = some v ∧ v.q = q := by
      intro m q ⟨d, hd, hdq⟩
      obtain ⟨_, v, hv, hr⟩ := hinv m
      rw [hr] at hd; cases hd
      exact ⟨v, hv, hdq⟩
    intro q s ⟨k, hk, hs, hlast⟩
    obtain hq' | hq' := hq q.val q.isLt
    · -- a ranked state: infinite descent after the last visit
      obtain ⟨r, hr, hrq⟩ := hq'
      have hoff : ∀ m, k < c.t0 + m → ∀ v, nodeAt c (sq m).1 = some v → v.q.val ≠ r.1 := by
        intro m hm v hv e
        apply hlast (c.t0 + m) hm
        obtain ⟨_, v0, hv0, hr0⟩ := hinv m
        rw [hv] at hv0; cases hv0
        exact ⟨_, hr0, Fin.ext (by show v.q.val = q.val; rw [e, hrq])⟩
      have hL := hlen r hr
      refine absurd (fun j => ?_) (no_descent (r.2.headD []).length
        (fun j => rval r.2 (sq (k + 1 + j))) (fun j => ?_))
      · obtain ⟨_, v, v', hv, hv', _, hdesc⟩ := hrel (k + 1 + j)
        exact hdesc r hr (hoff (k + 1 + j) (by omega) v hv) (hoff (k + 1 + j + 1) (by omega) v' hv')
      · obtain ⟨⟨v, succ, hv, _⟩, _⟩ := hinv (k + 1 + j)
        unfold rval
        simp only [List.length_map]
        unfold rankLen at hL
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hL
        cases e : r.2[(sq (k + 1 + j)).1]? with
        | none =>
          exfalso
          rw [List.getElem?_eq_none_iff, hL.1] at e
          rw [List.getElem?_eq_none e] at hv; cases hv
        | some a =>
          simp only [Option.getD_some]
          simpa using hL.2 a (List.mem_of_getElem? e)
    · -- an absent state: visited only in the prefix
      unfold absentOK at hq'
      simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, List.mem_range] at hq'
      obtain ⟨hnode, hpre⟩ := hq'
      have hkt : k < c.t0 := by
        apply Classical.byContradiction; intro hge
        obtain ⟨v, hv, hvq⟩ := hstate (k - c.t0) q (by rw [show c.t0 + (k - c.t0) = k by omega]; exact hk)
        cases e : c.nodes[(sq (k - c.t0)).1]? with
        | none => simp [nodeAt, e] at hv
        | some p =>
          simp only [nodeAt, e, Option.map_some', Option.some.injEq] at hv
          exact hnode p (List.mem_of_getElem? e) (by rw [← hvq, ← hv])
      obtain ⟨b, hb⟩ := (inState_iff hnh q k).1 hk
      have := hpre k (by omega)
      rw [lab, hlab0 k hkt] at hb
      rw [hb] at this
      simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq] at this
      omega

end sound

end Bbbb
