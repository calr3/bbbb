import Bbbb.Certs3.Chunks
import Bbbb.Champ3

/-!
# BBBB(3) = 127, assuming the holdouts

The kernel checks the tree of partial 3-state machines (`Certs3/`): every machine extends a
certified leaf (so `g ≤ 127`), halts, or extends one of the holdouts `holds3`.  The holdouts are
the hypothesis `Holds3Covered`, still to be proven.  The champion
`1RB1LB_0RC0LA_1LC0LA` (`Exact.lean`) gives 127 in each of the three models.
-/

namespace Bbbb

/-- every machine extending a holdout has `g ≤ 127` (to be proven) -/
def Holds3Covered : Prop := ∀ (k : Nat) (P : PM), holds3[k]? = some P → Covered 2 127 P

theorem good3 (hh : Holds3Covered) (M : Machine 3) : Good M 127 :=
  checkTree_sound decTr2_surj (chunks3_covered hh) _ _ top3_ok M
    (fun q b c h => by
      obtain ⟨q, hq⟩ := q
      match q, hq, b with
      | 0, _, false | 0, _, true | 1, _, false | 1, _, true | 2, _, false | 2, _, true =>
        simp [tIdx] at h
      | _ + 3, hq, _ => exact absurd hq (by omega))

set_option maxRecDepth 100000 in
theorem bbbb3_anySets (hh : Holds3Covered) : IsBBBB 2 anySets 127 :=
  ⟨fun M B O s _ h => good3 hh M B O s h, champ3, single 0 false, single 1 true, trivial,
    champ3_qq⟩

set_option maxRecDepth 100000 in
theorem bbbb3_oneEach (hh : Holds3Covered) : IsBBBB 2 oneEach 127 :=
  ⟨fun M B O s _ h => good3 hh M B O s h, champ3, single 0 false, single 1 true,
    ⟨0, false, 1, true, fun _ _ => rfl, fun _ _ => rfl⟩, champ3_qq⟩

set_option maxRecDepth 100000 in
theorem bbbb3_oneBoopRestBeep (hh : Holds3Covered) : IsBBBB 2 oneBoopRestBeep 127 :=
  ⟨fun M B O s _ h => good3 hh M B O s h, champ3, fun q b => !(q == 1 && b == true),
    single 1 true, ⟨1, true, fun _ _ => rfl, fun _ _ => rfl⟩,
    qq_of_cert (c := champ3Cert) (by decide) _ _ 126 (by decide)⟩

end Bbbb
