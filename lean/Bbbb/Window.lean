import Bbbb.Seq

/-!
# Symbolic simulation on a window of the tape

A window `⟨q, l, r⟩` stands for the configurations `⟨q, l ++ X, r ++ Y⟩` (`Win.den`), where each
tail is either blank (`Side.blank`) or arbitrary (`Side.any`).  `wrun` runs the machine on the
window and records the transitions taken; it fails if it would read an arbitrary tail.  If it
succeeds, every configuration the window stands for runs the same way (`wrun_sound`).

A run from the start configuration is a window run with both tails blank.  A window run that
comes back to its own window (`Ret`) repeats forever, which makes the transition sequence
eventually periodic (`lab_eq_seqv`): this covers cyclers and translated cyclers.
-/

namespace Bbbb

open TM

variable {Q : Type}

/-- `app l s`: the cells `l`, then `s` -/
def app : List Bool → Strm → Strm
  | [], s => s
  | b :: l, s => b ::: app l s

@[simp] theorem app_nil (s : Strm) : app [] s = s := rfl
@[simp] theorem app_cons (b : Bool) (l : List Bool) (s : Strm) :
    app (b :: l) s = b ::: app l s := rfl

theorem app_append (l m : List Bool) (s : Strm) : app (l ++ m) s = app l (app m s) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

theorem app_replicate_false (n : Nat) : app (List.replicate n false) blank = blank := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, app_cons, ih, cons_blank]

inductive Side
  | blank
  | any
deriving DecidableEq

/-- an admissible tail: blank for a blank side -/
def Adm : Side → Strm → Prop
  | .blank, X => X = blank
  | .any, _ => True

structure Win (Q : Type) where
  q : Q
  l : List Bool
  r : List Bool

def Win.den (w : Win Q) (X Y : Strm) : Cfg Q := ⟨w.q, app w.l X, app w.r Y⟩

/-- the symbol under the head, if the window knows it -/
def headR (kr : Side) : List Bool → Option Bool
  | b :: _ => some b
  | [] => match kr with
    | .blank => some false
    | .any => none

inductive Res (Q : Type)
  | ok (w : Win Q)
  | halt
  | stuck

/-- one step on a window -/
def wstep (M : Q → Bool → Option (Bool × Dir × Q)) (kl kr : Side) (w : Win Q) : Res Q :=
  match headR kr w.r with
  | none => .stuck
  | some b => match M w.q b with
    | none => .halt
    | some (x, .R, q') => .ok ⟨q', x :: w.l, w.r.tail⟩
    | some (x, .L, q') => match w.l with
      | c :: l' => .ok ⟨q', l', c :: x :: w.r.tail⟩
      | [] => match kl with
        | .blank => .ok ⟨q', [], false :: x :: w.r.tail⟩
        | .any => .stuck

/-- `n` steps on a window, with the transitions taken -/
def wrun (M : Q → Bool → Option (Bool × Dir × Q)) (kl kr : Side) :
    Nat → Win Q → Option (Win Q × List (Q × Bool))
  | 0, w => some (w, [])
  | n + 1, w => match headR kr w.r, wstep M kl kr w with
    | some b, .ok w' => (wrun M kl kr n w').map (fun x => (x.1, (w.q, b) :: x.2))
    | _, _ => none

/-! ## soundness -/

theorem headR_sound {kr : Side} {r : List Bool} {b : Bool} {Y : Strm} (hY : Adm kr Y)
    (h : headR kr r = some b) : app r Y 0 = b := by
  cases r with
  | cons c r => cases h; rfl
  | nil =>
    cases kr with
    | blank => cases h; rw [show Y = blank from hY]; rfl
    | any => cases h

theorem tail_sound {kr : Side} {r : List Bool} {Y : Strm} (hY : Adm kr Y)
    (h : (headR kr r).isSome) : tl (app r Y) = app r.tail Y := by
  cases r with
  | cons c r => rfl
  | nil =>
    cases kr with
    | blank => rw [show Y = blank from hY]; rfl
    | any => cases h

theorem wstep_ok {M : Q → Bool → Option (Bool × Dir × Q)} {kl kr : Side} {w w' : Win Q}
    {X Y : Strm} (hX : Adm kl X) (hY : Adm kr Y) {b : Bool} (hb : headR kr w.r = some b)
    (h : wstep M kl kr w = .ok w') :
    M w.q b ≠ none ∧ step M (w.den X Y) = some (w'.den X Y) := by
  obtain ⟨q, l, r⟩ := w
  have h0 := headR_sound hY hb
  have ht := tail_sound (r := r) hY (by rw [hb]; rfl)
  simp only [wstep, hb] at h
  simp only [Win.den] at h0 ht ⊢
  cases hM : M q b with
  | none => rw [hM] at h; cases h
  | some t =>
    obtain ⟨x, d, q'⟩ := t
    rw [hM] at h
    refine ⟨by simp, ?_⟩
    simp only [step, h0, hM]
    cases d with
    | R => cases h; simp [Win.den, ht]
    | L =>
      cases l with
      | cons c l' => cases h; simp [Win.den, ht]
      | nil =>
        cases kl with
        | blank =>
          cases h
          rw [show X = blank from hX]
          simp [Win.den, ht]
          rfl
        | any => cases h

theorem wstep_halt {M : Q → Bool → Option (Bool × Dir × Q)} {kl kr : Side} {w : Win Q}
    {X Y : Strm} (hY : Adm kr Y) {b : Bool} (hb : headR kr w.r = some b)
    (h : wstep M kl kr w = .halt) : M (w.den X Y).q ((w.den X Y).R 0) = none := by
  obtain ⟨q, l, r⟩ := w
  have h0 := headR_sound hY hb
  simp only [wstep, hb] at h
  simp only [Win.den] at h0 ⊢
  rw [h0]
  cases hM : M q b with
  | none => rfl
  | some t =>
    obtain ⟨x, d, q'⟩ := t
    rw [hM] at h
    cases d with
    | R => cases h
    | L =>
      cases l with
      | cons c l' => cases h
      | nil => cases kl <;> cases h

theorem labFrom_zero (M : Q → Bool → Option (Bool × Dir × Q)) (c : Cfg Q) :
    labFrom M c 0 = if (M c.q (c.R 0)).isSome then some (c.q, c.R 0) else none := rfl

theorem labFrom_add {M : Q → Bool → Option (Bool × Dir × Q)} {c c' : Cfg Q} {a : Nat}
    (h : run M a c = some c') (k : Nat) : labFrom M c (a + k) = labFrom M c' k := by
  unfold labFrom
  rw [run_add, h]
  rfl

theorem wrun_sound {M : Q → Bool → Option (Bool × Dir × Q)} {kl kr : Side} {X Y : Strm}
    (hX : Adm kl X) (hY : Adm kr Y) :
    ∀ n (w w' : Win Q) (ls : List (Q × Bool)), wrun M kl kr n w = some (w', ls) →
      run M n (w.den X Y) = some (w'.den X Y) ∧ ls.length = n ∧
      ∀ k, k < n → labFrom M (w.den X Y) k = ls[k]? := by
  intro n
  induction n with
  | zero =>
    intro w w' ls h
    simp only [wrun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    intro w w' ls h
    simp only [wrun] at h
    cases hb : headR kr w.r with
    | none => rw [hb] at h; cases h
    | some b =>
      cases hs : wstep M kl kr w with
      | halt => rw [hb, hs] at h; cases h
      | stuck => rw [hb, hs] at h; cases h
      | ok w1 =>
        simp only [hb, hs] at h
        cases hr : wrun M kl kr n w1 with
        | none => rw [hr] at h; cases h
        | some x =>
          obtain ⟨w2, ls2⟩ := x
          rw [hr] at h
          simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hdef, hst⟩ := wstep_ok hX hY hb hs
          obtain ⟨h1, h2, h3⟩ := ih w1 w2 ls2 hr
          have hrun1 : run M 1 (w.den X Y) = some (w1.den X Y) := by
            simp [run, Sys.run, hst]
          refine ⟨?_, by simp [h2], ?_⟩
          · rw [Nat.add_comm, run_add, hrun1]; exact h1
          · intro k hk
            cases k with
            | zero =>
              rw [labFrom_zero]
              have h0 := headR_sound (r := w.r) hY hb
              simp only [Win.den] at h0 ⊢
              rw [h0]
              cases hM : M w.q b with
              | none => exact absurd hM hdef
              | some _ => simp
            | succ k =>
              rw [show k + 1 = 1 + k from Nat.add_comm _ _, labFrom_add hrun1, h3 k (by omega),
                Nat.add_comm]
              simp

/-! ## returning windows -/

/-- `l` is a prefix of `m` -/
def isPre : List Bool → List Bool → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: m => a == b && isPre l m

theorem isPre_sound : ∀ {l m : List Bool}, isPre l m = true → ∃ e, m = l ++ e
  | [], m, _ => ⟨m, rfl⟩
  | _ :: _, [], h => by cases h
  | a :: l, b :: m, h => by
    simp only [isPre, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨e, rfl⟩ := isPre_sound h
    exact ⟨e, rfl⟩

/-- drop trailing blanks -/
def strip : List Bool → List Bool
  | [] => []
  | b :: l => if !b && (strip l).isEmpty then [] else b :: strip l

theorem app_strip (l : List Bool) : app (strip l) blank = app l blank := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [strip]
    cases b <;> cases hs : strip l <;> simp only [hs] at ih <;>
      simp [app_cons, ← ih, cons_blank]

/-- the side `l'` after a period is the side `l` with another admissible tail -/
def Ret : Side → List Bool → List Bool → Bool
  | .any, l, l' => isPre l l'
  | .blank, l, l' => strip l == strip l'

theorem Ret_sound {k : Side} {l l' : List Bool} {X : Strm} (h : Ret k l l' = true)
    (hX : Adm k X) : ∃ X', Adm k X' ∧ app l' X = app l X' := by
  cases k with
  | any =>
    obtain ⟨e, rfl⟩ := isPre_sound h
    exact ⟨app e X, trivial, app_append _ _ _⟩
  | blank =>
    refine ⟨blank, rfl, ?_⟩
    rw [show X = blank from hX, ← app_strip l', ← app_strip l]
    simp only [Ret, beq_iff_eq] at h
    rw [h]

/-- the window `l` fits the concrete side `lc` (whose tail is blank) -/
def Fit : Side → List Bool → List Bool → Bool
  | .any, l, lc => isPre l (lc ++ List.replicate l.length false)
  | .blank, l, lc => strip l == strip lc

theorem Fit_sound {k : Side} {l lc : List Bool} (h : Fit k l lc = true) :
    ∃ X, Adm k X ∧ app lc blank = app l X := by
  cases k with
  | any =>
    obtain ⟨e, he⟩ := isPre_sound h
    refine ⟨app e blank, trivial, ?_⟩
    rw [← app_append, ← he, app_append, app_replicate_false]
  | blank =>
    refine ⟨blank, rfl, ?_⟩
    rw [← app_strip lc, ← app_strip l]
    simp only [Fit, beq_iff_eq] at h
    rw [h]

/-- A window run that returns to its window repeats forever. -/
theorem labFrom_periodic {M : Q → Bool → Option (Bool × Dir × Q)} {kl kr : Side} {p : Nat}
    {w0 w1 : Win Q} {ls : List (Q × Bool)} (h : wrun M kl kr p w0 = some (w1, ls))
    (hq : w1.q = w0.q) (hl : Ret kl w0.l w1.l = true) (hr : Ret kr w0.r w1.r = true) :
    ∀ m X Y, Adm kl X → Adm kr Y → ∀ i, i < p →
      labFrom M (w0.den X Y) (m * p + i) = ls[i]? := by
  intro m
  induction m with
  | zero =>
    intro X Y hX hY i hi
    rw [Nat.zero_mul, Nat.zero_add]
    exact (wrun_sound hX hY p w0 w1 ls h).2.2 i hi
  | succ m ih =>
    intro X Y hX hY i hi
    obtain ⟨hrun, _, _⟩ := wrun_sound hX hY p w0 w1 ls h
    obtain ⟨X', hX', eX⟩ := Ret_sound hl hX
    obtain ⟨Y', hY', eY⟩ := Ret_sound hr hY
    have : w1.den X Y = w0.den X' Y' := by
      simp only [Win.den, hq, eX, eY]
    rw [Nat.succ_mul, show m * p + p + i = p + (m * p + i) by omega, labFrom_add hrun, this]
    exact ih X' Y' hX' hY' i hi

/-! ## eventually periodic sequences of transitions -/

/-- the sequence `pre`, then `per` repeated -/
def seqv {α : Type} (pre per : List α) (n : Nat) : Option α :=
  if n < pre.length then pre[n]? else per[(n - pre.length) % per.length]?

/-- the start window: blank tape -/
def winit {n : Nat} : Win (Fin (n + 1)) := ⟨0, [], []⟩

theorem winit_den {n : Nat} : (winit (n := n)).den blank blank = init := rfl

/-- A translated-cycler certificate: after `t0` steps from the start (transitions `ls0`), the
window `w0` (with tails `kl`, `kr`) fits the configuration and returns to itself after `p`
steps (transitions `ls`).  Then the transitions are `ls0`, then `ls` repeated. -/
theorem lab_eq_seqv {n : Nat} {M : Machine (n + 1)} {t0 p : Nat} {wc w0 w1 : Win (Fin (n + 1))}
    {ls0 ls : List (Fin (n + 1) × Bool)} {kl kr : Side} (hp : 0 < p)
    (h0 : wrun M .blank .blank t0 winit = some (wc, ls0))
    (hq0 : w0.q = wc.q) (hl0 : Fit kl w0.l wc.l = true) (hr0 : Fit kr w0.r wc.r = true)
    (h : wrun M kl kr p w0 = some (w1, ls))
    (hq : w1.q = w0.q) (hl : Ret kl w0.l w1.l = true) (hr : Ret kr w0.r w1.r = true) :
    ∀ k, lab M k = seqv ls0 ls k := by
  obtain ⟨hrun0, hlen0, hlab0⟩ := wrun_sound (kl := .blank) (kr := .blank) (X := blank) (Y := blank) rfl rfl t0 _ _ _ h0
  obtain ⟨_, hlen, _⟩ := wrun_sound (M := M) (X := blank) (Y := blank)
    (by cases kl <;> simp [Adm]) (by cases kr <;> simp [Adm]) p w0 w1 ls h
  obtain ⟨X0, hX0, eX0⟩ := Fit_sound hl0
  obtain ⟨Y0, hY0, eY0⟩ := Fit_sound hr0
  have hc : wc.den blank blank = w0.den X0 Y0 := by simp only [Win.den, hq0, eX0, eY0]
  intro k
  unfold seqv lab
  rw [winit_den] at hrun0 hlab0
  by_cases hk : k < ls0.length
  · rw [if_pos hk]; exact hlab0 k (by omega)
  · rw [if_neg hk, hlen0, hlen]
    rw [hlen0] at hk
    have e : k = t0 + ((k - t0) / p * p + (k - t0) % p) := by
      have := Nat.div_add_mod (k - t0) p; rw [Nat.mul_comm] at this; omega
    rw [e, labFrom_add hrun0, hc, labFrom_periodic h hq hl hr _ X0 Y0 hX0 hY0 _ (Nat.mod_lt _ hp)]
    congr 2
    omega

end Bbbb
