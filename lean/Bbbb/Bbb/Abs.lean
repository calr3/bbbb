import Bbbb.Bbb.Tail

/-!
# Abstract windows

An abstract node `⟨q, l, r, kl, kr⟩` stands for the configurations in state `q` whose left side
is `l` followed by a tail of kind `kl`, and whose right side (head cell first) is `r` followed by
a tail of kind `kr` (`den`).  `asucc` takes one step on a node: it splits off a tail cell when the
window does not know the cell it needs, and moves the cells beyond radius `R` into the tails.
Every configuration of a node steps to a configuration of one of its successors (`asucc_sound`),
and each successor carries, for each side, whether the measure of the tail strictly decreases
(`dec`), does not increase (`le`), or is unknown (`any`).
-/

namespace Bbbb

open TM

inductive Eff
  | dec
  | le
  | any
deriving DecidableEq, Repr

def Eff.ok : Eff → List Bool → List Bool → Prop
  | .dec, t, t' => mu t' < mu t
  | .le, t, t' => mu t' ≤ mu t
  | .any, _, _ => True

structure ANode (n : Nat) where
  q : Fin (n + 1)
  l : List Bool
  r : List Bool
  kl : TK
  kr : TK
deriving DecidableEq, Repr

def ANode.den {n : Nat} (v : ANode n) (tl tr : List Bool) : Cfg (Fin (n + 1)) :=
  ⟨v.q, app (v.l ++ tl) blank, app (v.r ++ tr) blank⟩

def decEff (d : Bool) : Eff := if d then .dec else .le

/-- keep the first `R` cells, push the others into the tail -/
def trunc (R : Nat) (sp : SP) (L : List Bool) (k : TK) (e : Eff) : List Bool × TK × Eff :=
  (L.take R, (L.drop R).foldr (push sp) k,
    if (L.drop R).isEmpty || (k == .blank && (L.drop R).all (· == false)) then e else .any)

theorem foldr_push_sound (sp : SP) : ∀ (ex : List Bool) {k : TK} {t : List Bool}, k.mem sp t →
    (ex.foldr (push sp) k).mem sp (ex ++ t)
  | [], _, _, h => h
  | c :: ex, _, _, h => push_sound sp c (foldr_push_sound sp ex h)

theorem foldr_push_false : ∀ (ex : List Bool), ex.all (· == false) = true →
    ex.foldr (push sp) .blank = .blank
  | [], _ => rfl
  | c :: ex, h => by
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.foldr_cons, foldr_push_false ex h, push]; rfl

theorem trunc_sound {R : Nat} {sp : SP} {L : List Bool} {k : TK} {e : Eff} {t t0 : List Bool}
    (hk : k.mem sp t) (he : e.ok t0 t) :
    app (L ++ t) blank = app ((trunc R sp L k e).1 ++ (L.drop R ++ t)) blank ∧
      (trunc R sp L k e).2.1.mem sp (L.drop R ++ t) ∧ (trunc R sp L k e).2.2.ok t0 (L.drop R ++ t) := by
  refine ⟨by simp only [trunc]; rw [← List.append_assoc, List.take_append_drop],
    foldr_push_sound sp _ hk, ?_⟩
  simp only [trunc]
  split
  · rename_i h
    simp only [Bool.or_eq_true, List.isEmpty_iff, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨rfl, h⟩
    · rw [h]; exact he
    · -- pushing blanks onto a blank tail keeps the measure `0`
      have ht : strip t = [] := hk
      have : mu (L.drop R ++ t) = mu t := by
        unfold mu
        rw [ht, (strip_eq_nil_iff _).2]
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · rw [List.all_eq_true] at h; simpa using h x hx
        · exact (strip_eq_nil_iff t).1 ht x hx
      cases e <;> simp only [Eff.ok] at he ⊢ <;> omega
  · trivial

variable {n : Nat}

/-- one step with the head cell `c` (the rest of the right window `r'`, of tail kind `kr'`) -/
def stepHead (M : Machine (n + 1)) (R : Nat) (spL spR : SP) (v : ANode n) (c : Bool)
    (r' : List Bool) (kr' : TK) (eR : Eff) : Option (List (Eff × Eff × ANode n)) :=
  match M v.q c with
  | none => none
  | some (x, .R, q') =>
    let t := trunc R spL (x :: v.l) v.kl .le
    some [(t.2.2, eR, ⟨q', t.1, r', t.2.1, kr'⟩)]
  | some (x, .L, q') => match v.l with
    | c' :: l' =>
      let t := trunc R spR (c' :: x :: r') kr' eR
      some [(.le, t.2.2, ⟨q', l', t.1, v.kl, t.2.1⟩)]
    | [] => some ((pop spL v.kl).map fun y =>
      let t := trunc R spR (y.1 :: x :: r') kr' eR
      (decEff y.2.2, t.2.2, ⟨q', [], t.1, y.2.1, t.2.1⟩))

def joinOpt {α : Type} : List (Option (List α)) → Option (List α)
  | [] => some []
  | x :: xs => x.bind fun a => (joinOpt xs).map (a ++ ·)

theorem mem_joinOpt {α : Type} : ∀ {xs : List (Option (List α))} {es : List α}, joinOpt xs = some es →
    ∀ x ∈ xs, ∃ a, x = some a ∧ ∀ y ∈ a, y ∈ es
  | [], _, _, x, hx => absurd hx (List.not_mem_nil _)
  | x :: xs, es, h, z, hz => by
    simp only [joinOpt] at h
    cases hx : x with
    | none => rw [hx] at h; cases h
    | some a =>
      cases hr : joinOpt xs with
      | none => rw [hx, hr] at h; cases h
      | some b =>
        rw [hx, hr] at h
        have h : a ++ b = es := by simpa using h
        subst h
        rcases List.mem_cons.1 hz with rfl | hz
        · exact ⟨a, hx, fun y hy => List.mem_append_left _ hy⟩
        · obtain ⟨a', ha', hy⟩ := mem_joinOpt hr z hz
          exact ⟨a', ha', fun y h => List.mem_append_right _ (hy y h)⟩

/-- the successors of a node, `none` if some configuration of it halts -/
def asucc (M : Machine (n + 1)) (R : Nat) (spL spR : SP) (v : ANode n) :
    Option (List (Eff × Eff × ANode n)) :=
  match v.r with
  | c :: r' => stepHead M R spL spR v c r' v.kr .le
  | [] => joinOpt ((pop spR v.kr).map fun y => stepHead M R spL spR v y.1 [] y.2.1 (decEff y.2.2))

/-- the successor relation on concrete tails -/
def Adv (M : Machine (n + 1)) (spL spR : SP) (v : ANode n) (tl tr : List Bool)
    (e : Eff × Eff × ANode n) : Prop :=
  ∃ tl' tr', step M (v.den tl tr) = some (e.2.2.den tl' tr') ∧ e.2.2.kl.mem spL tl' ∧
    e.2.2.kr.mem spR tr' ∧ e.1.ok tl tl' ∧ e.2.1.ok tr tr'

theorem decEff_ok {d : Bool} {t t' : List Bool} (h1 : mu t' ≤ mu t) (h2 : d = true → mu t' < mu t) :
    (decEff d).ok t t' := by
  cases d
  · exact h1
  · exact h2 rfl

theorem stepHead_sound {M : Machine (n + 1)} {R : Nat} {spL spR : SP} {v : ANode n} {c : Bool}
    {r' : List Bool} {kr' : TK} {eR : Eff} {es : List (Eff × Eff × ANode n)}
    (h : stepHead M R spL spR v c r' kr' eR = some es) {tl tr tr' : List Bool}
    (hl : v.kl.mem spL tl) (hr : kr'.mem spR tr') (he : eR.ok tr tr')
    (hR : app (v.r ++ tr) blank = c ::: app (r' ++ tr') blank) :
    ∃ e ∈ es, Adv M spL spR v tl tr e := by
  unfold stepHead at h
  have hstep : ∀ x d q', M v.q c = some (x, d, q') → step M (v.den tl tr) = some (match d with
      | Dir.R => ⟨q', x ::: app (v.l ++ tl) blank, app (r' ++ tr') blank⟩
      | Dir.L => ⟨q', TM.tl (app (v.l ++ tl) blank),
          app (v.l ++ tl) blank 0 ::: x ::: app (r' ++ tr') blank⟩) := by
    intro x d q' hM
    cases d <;> simp only [step, ANode.den, hR, cons_zero, hM, tl_cons]
  cases hM : M v.q c with
  | none => rw [hM] at h; cases h
  | some tr0 =>
    obtain ⟨x, d, q'⟩ := tr0
    have hstep := hstep x d q' hM
    rw [hM] at h
    cases d with
    | R =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      have ht := trunc_sound (R := R) (L := x :: v.l) (e := .le) (t0 := tl) hl (Nat.le_refl _)
      refine ⟨_, tr', ?_, ht.2.1, hr, ht.2.2, he⟩
      rw [hstep]
      simp only [ANode.den, Option.some.injEq]
      rw [← ht.1]; rfl
    | L =>
      simp only at h
      cases hvl : v.l with
      | cons c' l' =>
        rw [hvl] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        have ht := trunc_sound (R := R) (sp := spR) (L := c' :: x :: r') hr he
        refine ⟨tl, _, ?_, hl, ht.2.1, Nat.le_refl _, ht.2.2⟩
        rw [hstep, hvl]
        simp only [ANode.den, Option.some.injEq]
        rw [← ht.1]; rfl
      | nil =>
        rw [hvl] at h
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨y, hy, tl', htl, hk, h1, h2⟩ := pop_sound spL hl
        refine ⟨_, List.mem_map_of_mem _ hy, ?_⟩
        have ht := trunc_sound (R := R) (sp := spR) (L := y.1 :: x :: r') hr he
        refine ⟨tl', _, ?_, hk, ht.2.1, decEff_ok h1 h2, ht.2.2⟩
        rw [hstep, hvl]
        simp only [ANode.den, Option.some.injEq, List.nil_append] at htl ⊢
        rw [htl, ← ht.1]; rfl

theorem asucc_sound {M : Machine (n + 1)} {R : Nat} {spL spR : SP} {v : ANode n}
    {es : List (Eff × Eff × ANode n)} (h : asucc M R spL spR v = some es) {tl tr : List Bool}
    (hl : v.kl.mem spL tl) (hr : v.kr.mem spR tr) : ∃ e ∈ es, Adv M spL spR v tl tr e := by
  unfold asucc at h
  cases hvr : v.r with
  | cons c r' =>
    rw [hvr] at h
    exact stepHead_sound h hl hr (Nat.le_refl _) (by rw [hvr]; rfl)
  | nil =>
    rw [hvr] at h
    obtain ⟨y, hy, tr', htr, hk, h1, h2⟩ := pop_sound spR hr
    obtain ⟨a, ha, hsub⟩ := mem_joinOpt h _ (List.mem_map_of_mem _ hy)
    obtain ⟨e, he, hadv⟩ := stepHead_sound ha hl hk (decEff_ok h1 h2)
      (by rw [hvr]; simpa using htr)
    exact ⟨e, hsub e he, hadv⟩

end Bbbb
