import Bbbb.Window

/-!
# A certified decider: halting machines, cyclers and translated cyclers

A certificate says that the machine halts (`Cert.halt`), or that its transitions are eventually
periodic (`Cert.per`, checked by `lab_eq_seqv`).  For an eventually periodic machine `crit`
checks that every transition of the period occurs a second time after the preperiod and before
step `K`.  Then every boop set either misses the period (no boop after the preperiod, so no
`g`) or has two boops after the preperiod before step `K`, which gives `g ≤ K` whatever the beep
set (`good_of_crit`).
-/

namespace Bbbb

open TM

/-- `g ≤ K` for every beep set and boop set -/
def Good {n : Nat} (M : Machine (n + 1)) (K : Nat) : Prop :=
  ∀ B O t, M.QQHaltsAt B O t → t ≤ K

inductive Cert
  /-- the transition at step `t` is undefined -/
  | halt (t : Nat)
  /-- after `t0` steps, the window `l`, `r` (tails `kl`, `kr`) returns after `p` steps -/
  | per (t0 p : Nat) (l r : List Bool) (kl kr : Side)
  /-- not decided here -/
  | holdout

/-- every transition of the period occurs again after the preperiod, before step `K` -/
def crit {α : Type} [DecidableEq α] (pre per : List α) (K : Nat) : Bool :=
  (List.range per.length).all (fun d => decide (pre.length + d < K) &&
    (List.range (K - pre.length)).any (fun e => e != d &&
      decide (seqv pre per (pre.length + e) = seqv pre per (pre.length + d))))

def checkCert {n : Nat} (M : Machine (n + 1)) (K : Nat) : Cert → Bool
  | .halt t => match wrun M .blank .blank t winit with
    | none => false
    | some (wc, _) => match wstep M .blank .blank wc with
      | .halt => true
      | _ => false
  | .per t0 p l r kl kr => match wrun M .blank .blank t0 winit with
    | none => false
    | some (wc, ls0) => Fit kl l wc.l && Fit kr r wc.r &&
      match wrun M kl kr p ⟨wc.q, l, r⟩ with
      | none => false
      | some (w1, ls) => decide (0 < p) && decide (w1.q = wc.q) && Ret kl l w1.l &&
          Ret kr r w1.r && crit ls0 ls K
  | .holdout => false

/-! ## soundness -/

theorem ev_none {n : Nat} {S : TSet (n + 1)} {M : Machine (n + 1)} {k : Nat}
    (h : lab M k = none) : ev S M k = false := by
  unfold ev; rw [h]

/-- the event of an optional transition -/
def evq {n : Nat} (S : TSet (n + 1)) : Option (Fin (n + 1) × Bool) → Bool
  | none => false
  | some (q, b) => S q b

theorem ev_eq {n : Nat} (S : TSet (n + 1)) (M : Machine (n + 1)) (k : Nat) :
    ev S M k = evq S (lab M k) := by
  unfold ev evq; cases lab M k <;> rfl

theorem seqv_periodic {α : Type} (pre per : List α) (n : Nat) (hn : pre.length ≤ n) :
    seqv pre per (n + per.length) = seqv pre per n := by
  unfold seqv
  rw [if_neg (by omega), if_neg (by omega),
    show n + per.length - pre.length = (n - pre.length) + per.length by omega, Nat.add_mod_right]

theorem good_of_crit {n : Nat} {M : Machine (n + 1)} {K : Nat}
    {pre per : List (Fin (n + 1) × Bool)} (hp : 0 < per.length) (hc : crit pre per K = true)
    (hlab : ∀ k, lab M k = seqv pre per k) : Good M K := by
  intro B O t h
  have hper : ∀ S : TSet (n + 1), Periodic (ev S M) pre.length per.length := by
    intro S k hk
    rw [ev_eq, ev_eq, hlab, hlab, seqv_periodic _ _ _ hk]
  unfold crit at hc
  rw [List.all_eq_true] at hc
  by_cases hb : ∃ d, d < per.length ∧ ev O M (pre.length + d) = true
  · obtain ⟨d, hd, hO⟩ := hb
    have := hc d (List.mem_range.2 hd)
    rw [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at this
    obtain ⟨hdK, e, he, hed⟩ := this
    rw [List.mem_range] at he
    rw [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hed
    obtain ⟨hne, hseq⟩ := hed
    have hO' : ev O M (pre.length + e) = true := by
      rw [ev_eq, hlab, hseq, ← hlab, ← ev_eq]; exact hO
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := le_of_periodic (T := K - 1) hp (hper B) (hper O) (i := pre.length + e)
        (j := pre.length + d) (by omega) (by omega) (by omega) hO' hO h
      omega
    · have := le_of_periodic (T := K - 1) hp (hper B) (hper O) (i := pre.length + d)
        (j := pre.length + e) (by omega) (by omega) (by omega) hO hO' h
      omega
  · exact absurd h (not_of_periodic hp (hper O) (fun k h1 h2 => by
      cases e : ev O M k
      · rfl
      · exact absurd ⟨k - pre.length, by omega, by rw [show pre.length + (k - pre.length) = k by omega]; exact e⟩ hb))

theorem headR_blank (r : List Bool) : ∃ b, headR .blank r = some b := by
  cases r with
  | nil => exact ⟨false, rfl⟩
  | cons b _ => exact ⟨b, rfl⟩

theorem good_of_halt {n : Nat} {M : Machine (n + 1)} {K t : Nat} {wc : Win (Fin (n + 1))}
    {ls : List (Fin (n + 1) × Bool)} (h0 : wrun M .blank .blank t winit = some (wc, ls))
    (hh : wstep M .blank .blank wc = .halt) : Good M K := by
  intro B O s h
  obtain ⟨hrun, _, _⟩ := wrun_sound (kl := .blank) (kr := .blank) (X := blank) (Y := blank)
    rfl rfl t _ _ _ h0
  rw [winit_den] at hrun
  obtain ⟨b, hb⟩ := headR_blank wc.r
  have hM := wstep_halt (kr := .blank) (X := blank) (Y := blank) rfl hb hh
  have hnone : ∀ k, lab M (t + k) = none := by
    intro k
    unfold lab
    rw [labFrom_add hrun]
    cases k with
    | zero => rw [labFrom_zero, hM]; rfl
    | succ k =>
      unfold labFrom
      have : run M (k + 1) (wc.den blank blank) = none := by
        rw [show k + 1 = 1 + k from Nat.add_comm _ _, run_add]
        simp [run, Sys.run, step, hM]
      rw [this]
  exact absurd h (not_of_finite (T := t) (fun k hk => by
    rw [show k = t + (k - t) by omega]; exact ev_none (hnone _)))

theorem checkCert_sound {n : Nat} {M : Machine (n + 1)} {K : Nat} {c : Cert}
    (h : checkCert M K c = true) : Good M K := by
  cases c with
  | holdout => cases h
  | halt t =>
    simp only [checkCert] at h
    cases h0 : wrun M .blank .blank t winit with
    | none => rw [h0] at h; cases h
    | some x =>
      obtain ⟨wc, ls⟩ := x
      rw [h0] at h
      simp only at h
      cases hs : wstep M .blank .blank wc with
      | halt => exact good_of_halt h0 hs
      | ok _ => rw [hs] at h; cases h
      | stuck => rw [hs] at h; cases h
  | per t0 p l r kl kr =>
    simp only [checkCert] at h
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
        obtain ⟨⟨⟨⟨hp, hq⟩, hl⟩, hr⟩, hc⟩ := h
        have hlab := lab_eq_seqv (w0 := ⟨wc.q, l, r⟩) hp h0 rfl hl0 hr0 h1 hq hl hr
        have hlen := (wrun_sound (M := M) (X := blank) (Y := blank)
          (by cases kl <;> simp [Adm]) (by cases kr <;> simp [Adm]) p _ w1 ls h1).2.1
        exact good_of_crit (by omega) hc hlab

end Bbbb
