import Bbbb.Core.Basic

/-!
# Mirror images

`mirror δ` is `δ` with every move reversed; `Cfg.mir` is the configuration seen in a mirror
(the head stays on its cell).  A run of `δ` is, in the mirror, a run of `mirror δ`
(`Reach.mir`), so a routine that is the mirror image of another needs no proof of its own.
-/

namespace TM

variable {Q : Type}

def Dir.flip : Dir → Dir
  | Dir.L => Dir.R
  | Dir.R => Dir.L

def mirror (δ : Q → Bool → Option (Bool × Dir × Q)) : Q → Bool → Option (Bool × Dir × Q) :=
  fun q b => (δ q b).map (fun t => (t.1, t.2.1.flip, t.2.2))

/-- the configuration seen in a mirror: the head on the same cell -/
def Cfg.mir (c : Cfg Q) : Cfg Q := ⟨c.q, tl c.R, c.R 0 ::: c.L⟩

theorem Cfg.mir_mir (c : Cfg Q) : c.mir.mir = c := by
  obtain ⟨q, L, R⟩ := c
  simp only [Cfg.mir]
  rw [cons_zero, tl_cons, cons_head_tl]

theorem mirror_mirror (δ : Q → Bool → Option (Bool × Dir × Q)) : mirror (mirror δ) = δ := by
  funext q b
  simp only [mirror, Option.map_map]
  cases δ q b with
  | none => rfl
  | some t => obtain ⟨w, d, q'⟩ := t; cases d <;> rfl

theorem step_mir (δ : Q → Bool → Option (Bool × Dir × Q)) (c : Cfg Q) :
    step (mirror δ) c.mir = (step δ c).map Cfg.mir := by
  obtain ⟨q, L, R⟩ := c
  simp only [step, Cfg.mir, mirror, cons_zero]
  cases δ q (R 0) with
  | none => rfl
  | some t =>
    obtain ⟨w, d, q'⟩ := t
    cases d with
    | R => rfl
    | L =>
      show some (⟨q', w ::: tl R, L⟩ : Cfg Q) = some (⟨q', tl (L 0 ::: w ::: tl R), (L 0 ::: w ::: tl R) 0 ::: tl L⟩)
      rw [tl_cons, cons_zero, cons_head_tl]

theorem run_mir (δ : Q → Bool → Option (Bool × Dir × Q)) :
    ∀ n (c : Cfg Q), run (mirror δ) n c.mir = (run δ n c).map Cfg.mir := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
    intro c
    show Sys.run (step (mirror δ)) (n + 1) c.mir = (Sys.run (step δ) (n + 1) c).map Cfg.mir
    simp only [Sys.run, step_mir]
    cases step δ c with
    | none => rfl
    | some c' => exact ih c'

theorem Reach.mir {δ : Q → Bool → Option (Bool × Dir × Q)} {a b : Cfg Q} (h : Reach δ a b) :
    Reach (mirror δ) a.mir b.mir := by
  obtain ⟨n, hn⟩ := h
  have hn : run δ n a = some b := hn
  exact ⟨n, by show run (mirror δ) n a.mir = some b.mir; rw [run_mir, hn]; rfl⟩

/-- a run of the mirror machine, seen in the mirror, is a run of the machine -/
theorem Reach.of_mir {δ : Q → Bool → Option (Bool × Dir × Q)} {a b : Cfg Q}
    (h : Reach (mirror δ) a b) : Reach δ a.mir b.mir := by
  have := Reach.mir h
  rwa [mirror_mirror] at this

/-- a template machine embedded in `δ` by a state map: its runs are runs of `δ` -/
theorem Reach.embed {Q' : Type} {δ : Q → Bool → Option (Bool × Dir × Q)}
    {δ' : Q' → Bool → Option (Bool × Dir × Q')} {φ : Q → Q'}
    (h : ∀ q b, Compat φ (δ q b) (δ' (φ q) b)) {a b : Cfg Q} (hr : Reach δ a b) :
    Reach δ' (a.map φ) (b.map φ) :=
  let ⟨n, hn⟩ := hr; ⟨n, sim_run δ δ' φ h n a b hn⟩

end TM
