import Bbbb.Bbb.Leaf

/-!
# Abstract tape tails

A tail (the cells beyond a window, nearest first, blank after the list) is abstracted by a kind
(`TK`): blank, nonblank, anything, or one of two families given by side parameters `a`, `w`
(`SP`): `a[i:] a^m w` (`A i`, any `m`) and `w[j:]` (`W j`).  The measure of a tail is the length
of its stripped list (`mu`).  `pop` splits off the nearest cell, `push` adds a nearer cell; both
are sound (`pop_sound`, `push_sound`), and `pop` reports when the measure strictly decreases.
-/

namespace Bbbb

open TM

/-! ## strip and the measure -/

/-- the stripped list of `b :: l`, from that of `l` -/
def consS (b : Bool) (s : List Bool) : List Bool := if !b && s.isEmpty then [] else b :: s

theorem strip_cons (b : Bool) (l : List Bool) : strip (b :: l) = consS b (strip l) := rfl

theorem app_eq_of_strip {t t' : List Bool} (h : strip t = strip t') : app t blank = app t' blank := by
  rw [← app_strip t, h, app_strip]

theorem strip_eq_nil_iff : ∀ l : List Bool, strip l = [] ↔ ∀ x ∈ l, x = false
  | [] => by simp [strip]
  | b :: l => by
    rw [strip_cons, consS]
    have ih := strip_eq_nil_iff l
    cases b <;> cases h : strip l <;> simp_all

theorem strip_ne_nil_of_any {l : List Bool} (h : l.any id = true) : strip l ≠ [] := by
  intro e
  rw [strip_eq_nil_iff] at e
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hx'⟩ := h
  rw [e x hx] at hx'; cases hx'

/-- the measure of a tail -/
def mu (t : List Bool) : Nat := (strip t).length

theorem mu_le_cons (c : Bool) (t : List Bool) : mu t ≤ mu (c :: t) := by
  unfold mu; rw [strip_cons, consS]
  split
  · rename_i h; simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
    rw [h.2]; simp
  · simp

theorem mu_lt_cons {c : Bool} {t : List Bool} (h : strip (c :: t) ≠ []) : mu t < mu (c :: t) := by
  unfold mu; rw [strip_cons, consS] at h ⊢
  split
  · rename_i h'; rw [if_pos h'] at h; exact absurd rfl h
  · simp

theorem mu_of_strip {t t' : List Bool} (h : strip t = strip t') : mu t = mu t' := by
  unfold mu; rw [h]

/-! ## kinds -/

inductive TK
  | blank
  | nb
  | any
  | A (i : Nat)
  | W (j : Nat)
deriving DecidableEq, Repr

/-- side parameters: the loop word `a` and the final word `w` -/
structure SP where
  a : List Bool
  w : List Bool
deriving DecidableEq, Repr

def rpt (a : List Bool) : Nat → List Bool
  | 0 => []
  | m + 1 => a ++ rpt a m

/-- the tail `t` has kind `k` -/
def TK.mem (sp : SP) : TK → List Bool → Prop
  | .blank, t => strip t = []
  | .nb, t => strip t ≠ []
  | .any, _ => True
  | .A i, t => ∃ m, strip t = strip (sp.a.drop i ++ rpt sp.a m ++ sp.w)
  | .W j, t => strip t = strip (sp.w.drop j)

/-- the nearest cell, the kind of the rest, and whether the measure decreases -/
def pop (sp : SP) : TK → List (Bool × TK × Bool)
  | .blank => [(false, .blank, false)]
  | .any => [(false, .any, false), (true, .any, false)]
  | .nb => [(true, .blank, true), (true, .nb, true), (false, .nb, true)]
  | .W j => match sp.w[j]? with
    | some c => [(c, .W (j + 1), (sp.w.drop j).any id)]
    | none => [(false, .blank, false)]
  | .A i => match sp.a[i]? with
    | some c =>
      if i + 1 < sp.a.length then [(c, .A (i + 1), (sp.a.drop i ++ sp.w).any id)]
      else [(c, .A 0, (sp.a.drop i ++ sp.w).any id), (c, .W 0, (sp.a.drop i ++ sp.w).any id)]
    | none => [(false, .any, false), (true, .any, false)]

/-- the kind of `c :: t` for `t` of kind `k` -/
def push (sp : SP) (c : Bool) : TK → TK
  | .nb => .nb
  | .any => if c then .nb else .any
  | .blank =>
    if !c then .blank else
    match sp.w.getLast? with
    | some x => if x = c then .W (sp.w.length - 1) else .nb
    | none => match sp.a.getLast? with
      | some x => if x = c then .A (sp.a.length - 1) else .nb
      | none => .nb
  | .W j =>
    if 0 < j ∧ sp.w[j - 1]? = some c then .W (j - 1)
    else if j = 0 ∧ sp.a.getLast? = some c then .A (sp.a.length - 1)
    else if c then .nb else .any
  | .A i =>
    if 0 < i ∧ sp.a[i - 1]? = some c then .A (i - 1)
    else if i = 0 ∧ sp.a.getLast? = some c then .A (sp.a.length - 1)
    else if c then .nb else .any

/-! ## soundness -/

theorem drop_getLast {a : List Bool} {c : Bool} (h : a.getLast? = some c) :
    a.drop (a.length - 1) = [c] := by
  induction a with
  | nil => cases h
  | cons x a ih =>
    cases a with
    | nil => simp at h; subst h; rfl
    | cons y a =>
      rw [List.getLast?_cons_cons] at h
      have := ih h
      simpa using this

theorem drop_pred {l : List Bool} {j : Nat} {c : Bool} (hj : 0 < j) (h : l[j - 1]? = some c) :
    l.drop (j - 1) = c :: l.drop j := by
  have hl : j - 1 < l.length := by
    rcases Nat.lt_or_ge (j - 1) l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.drop_eq_getElem_cons hl, show j - 1 + 1 = j by omega]
  rw [List.getElem?_eq_getElem hl] at h
  cases h; rfl

theorem consS_congr {t t' : List Bool} (c : Bool) (h : strip t = strip t') :
    strip (c :: t) = strip (c :: t') := by rw [strip_cons, strip_cons, h]

theorem push_sound (sp : SP) (c : Bool) {k : TK} {t : List Bool} (h : k.mem sp t) :
    (push sp c k).mem sp (c :: t) := by
  have nbT : c = true → TK.mem sp .nb (c :: t) := by
    intro hc; subst hc; simp [TK.mem, strip_cons, consS]
  cases k with
  | nb =>
    simp only [push, TK.mem] at h ⊢
    rw [strip_cons, consS]; split
    · rename_i h'; simp only [Bool.and_eq_true, List.isEmpty_iff] at h'; exact absurd h'.2 h
    · simp
  | any =>
    simp only [push]; split
    · exact nbT ‹_›
    · trivial
  | blank =>
    simp only [TK.mem] at h
    simp only [push]
    cases c with
    | false => simp [TK.mem, strip_cons, consS, h]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split
      · rename_i x hx
        split
        · rename_i hxc; subst hxc
          simp only [TK.mem]; rw [drop_getLast hx, strip_cons, h]; rfl
        · exact nbT rfl
      · rename_i hw
        split
        · rename_i x hx
          split
          · rename_i hxc; subst hxc
            refine ⟨0, ?_⟩
            have hw' : sp.w = [] := by
              cases e : sp.w with
              | nil => rfl
              | cons _ _ => rw [e] at hw; simp at hw
            rw [drop_getLast hx, hw', strip_cons, h]; rfl
          · exact nbT rfl
        · exact nbT rfl
  | W j =>
    simp only [TK.mem] at h
    simp only [push]
    split
    · rename_i hj
      simp only [TK.mem]; rw [drop_pred hj.1 hj.2]; exact consS_congr c h
    · split
      · rename_i hj
        obtain ⟨rfl, hl⟩ := hj
        refine ⟨0, ?_⟩
        rw [drop_getLast hl]
        simp only [List.drop_zero] at h
        simp only [rpt, List.append_nil, List.singleton_append]
        exact consS_congr c h
      · split
        · exact nbT ‹_›
        · trivial
  | A i =>
    obtain ⟨m, hm⟩ := h
    simp only [push]
    split
    · rename_i hi
      refine ⟨m, ?_⟩
      rw [drop_pred hi.1 hi.2]
      exact consS_congr c hm
    · split
      · rename_i hi
        obtain ⟨rfl, hl⟩ := hi
        refine ⟨m + 1, ?_⟩
        rw [drop_getLast hl]
        simp only [List.drop_zero] at hm
        simp only [rpt, List.singleton_append, List.cons_append, List.append_assoc] at hm ⊢
        exact consS_congr c hm
      · split
        · exact nbT ‹_›
        · trivial

theorem pop_sound (sp : SP) {k : TK} {t : List Bool} (h : k.mem sp t) :
    ∃ x ∈ pop sp k, ∃ t', app t blank = x.1 ::: app t' blank ∧ x.2.1.mem sp t' ∧
      mu t' ≤ mu t ∧ (x.2.2 = true → mu t' < mu t) := by
  -- generic: from a list `u` with the same strip as `t`
  have gen : ∀ (c : Bool) (t' : List Bool), strip t = strip (c :: t') →
      app t blank = c ::: app t' blank ∧ mu t' ≤ mu t ∧ (strip (c :: t') ≠ [] → mu t' < mu t) := by
    intro c t' e
    refine ⟨by rw [app_eq_of_strip e]; rfl, ?_, ?_⟩
    · rw [mu_of_strip e]; exact mu_le_cons c t'
    · intro hne; rw [mu_of_strip e]; exact mu_lt_cons hne
  cases k with
  | blank =>
    refine ⟨_, List.mem_singleton_self _, [], ?_⟩
    simp only [TK.mem] at h ⊢
    have := gen false [] (by rw [h]; rfl)
    exact ⟨this.1, rfl, this.2.1, fun h => by cases h⟩
  | any =>
    cases t with
    | nil =>
      refine ⟨(false, .any, false), by simp [pop], [], ?_, trivial, by simp [mu, strip], by simp⟩
      simp only [app_nil]; exact cons_blank.symm
    | cons b t =>
      refine ⟨(b, .any, false), by cases b <;> simp [pop], t, rfl, trivial, mu_le_cons b t, by simp⟩
  | nb =>
    simp only [TK.mem] at h
    cases t with
    | nil => exact absurd rfl h
    | cons b t =>
      have hl : mu t < mu (b :: t) := mu_lt_cons h
      have hst : strip t ≠ [] ∨ b = true := by
        rw [strip_cons, consS] at h
        cases b <;> cases e : strip t <;> simp_all
      cases b with
      | false =>
        have hs : strip t ≠ [] := by simpa using hst
        exact ⟨(false, .nb, true), by simp [pop], t, rfl, hs, Nat.le_of_lt hl, fun _ => hl⟩
      | true =>
        by_cases hs : strip t = []
        · exact ⟨(true, .blank, true), by simp [pop], t, rfl, hs, Nat.le_of_lt hl, fun _ => hl⟩
        · exact ⟨(true, .nb, true), by simp [pop], t, rfl, hs, Nat.le_of_lt hl, fun _ => hl⟩
  | W j =>
    simp only [TK.mem] at h
    cases hw : sp.w[j]? with
    | none =>
      have hd : sp.w.drop j = [] := by
        rw [List.drop_eq_nil_iff]
        rcases Nat.lt_or_ge j sp.w.length with h' | h'
        · rw [List.getElem?_eq_getElem h'] at hw; cases hw
        · exact h'
      rw [hd] at h
      refine ⟨(false, .blank, false), by simp [pop, hw], [], ?_⟩
      have := gen false [] (by rw [h]; rfl)
      exact ⟨this.1, rfl, this.2.1, fun h => by cases h⟩
    | some c =>
      have hj : j < sp.w.length := by
        rcases Nat.lt_or_ge j sp.w.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at hw; cases hw
      have hd : sp.w.drop j = c :: sp.w.drop (j + 1) := by
        rw [List.drop_eq_getElem_cons hj]; rw [List.getElem?_eq_getElem hj] at hw; cases hw; rfl
      refine ⟨(c, .W (j + 1), (sp.w.drop j).any id), by simp [pop, hw], sp.w.drop (j + 1), ?_⟩
      have := gen c _ (by rw [h, hd])
      refine ⟨this.1, rfl, this.2.1, fun ha => this.2.2 ?_⟩
      rw [← hd]; exact strip_ne_nil_of_any ha
  | A i =>
    obtain ⟨m, hm⟩ := h
    cases ha : sp.a[i]? with
    | none =>
      cases t with
      | nil =>
        refine ⟨(false, .any, false), by simp [pop, ha], [], ?_, trivial, by simp [mu, strip], by simp⟩
        simp only [app_nil]; exact cons_blank.symm
      | cons b t =>
        refine ⟨(b, .any, false), by cases b <;> simp [pop, ha], t, rfl, trivial, mu_le_cons b t,
          by simp⟩
    | some c =>
      have hi : i < sp.a.length := by
        rcases Nat.lt_or_ge i sp.a.length with h' | h'
        · exact h'
        · rw [List.getElem?_eq_none h'] at ha; cases ha
      have hd : sp.a.drop i = c :: sp.a.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons hi]; rw [List.getElem?_eq_getElem hi] at ha; cases ha; rfl
      have hany : (sp.a.drop i ++ sp.w).any id = true →
          strip (c :: (sp.a.drop (i + 1) ++ rpt sp.a m ++ sp.w)) ≠ [] := by
        intro hx
        apply strip_ne_nil_of_any
        rw [← List.cons_append, ← List.cons_append, ← hd]
        simp only [List.any_append, Bool.or_eq_true] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
      have g := gen c (sp.a.drop (i + 1) ++ rpt sp.a m ++ sp.w)
        (by rw [hm, hd]; rfl)
      by_cases hlt : i + 1 < sp.a.length
      · refine ⟨(c, .A (i + 1), (sp.a.drop i ++ sp.w).any id), by simp [pop, ha, hlt], _, g.1,
          ⟨m, rfl⟩, g.2.1, fun hx => g.2.2 (hany hx)⟩
      · have hd1 : sp.a.drop (i + 1) = [] := List.drop_eq_nil_iff.2 (by omega)
        rw [hd1, List.nil_append] at g
        cases m with
        | zero =>
          refine ⟨(c, .W 0, (sp.a.drop i ++ sp.w).any id), by simp [pop, ha, hlt], sp.w, ?_,
            rfl, g.2.1, fun hx => g.2.2 (by have := hany hx; rwa [hd1] at this)⟩
          simpa [rpt] using g.1
        | succ m =>
          refine ⟨(c, .A 0, (sp.a.drop i ++ sp.w).any id), by simp [pop, ha, hlt],
            rpt sp.a (m + 1) ++ sp.w, g.1, ⟨m, by simp [rpt]⟩, g.2.1,
            fun hx => g.2.2 (by have := hany hx; rwa [hd1] at this)⟩

end Bbbb
