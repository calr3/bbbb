import Bbbb.Enum2
import Bbbb.Holdouts
import Bbbb.Witness

/-!
# BBBB(1) = 2 and BBBB(2) = 18, in each of the three models
-/

namespace Bbbb

/-! ## one state -/

theorem certs1_ok :
    (List.range 25).all (fun i => checkCert (ofCodes1 (i / 5) (i % 5)) 2 (certs1.getD i .holdout))
      = true := by decide

theorem good1 (M : Machine 1) : Good M 2 := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_codes1 M
  have h := certs1_ok
  rw [List.all_eq_true] at h
  have h' := h (5 * a + b) (List.mem_range.2 (by omega))
  rw [show (5 * a + b) / 5 = a by omega, show (5 * a + b) % 5 = b by omega] at h'
  exact checkCert_sound h'

/-- `A0 = 0RA`: a boop at every step -/
def champ1 : Machine 1 := ofCodes1 1 0

theorem champ1_qq (B : TSet 1) : champ1.QQHaltsAt B (single 0 false) 2 := by
  have hlab : ∀ k, lab champ1 k = seqv [] [((0 : Fin 1), false)] k :=
    lab_eq_seqv (t0 := 0) (p := 1) (kl := .blank) (kr := .blank) (wc := ⟨0, [], []⟩)
      (w0 := ⟨0, [], []⟩) (w1 := ⟨0, [false], []⟩) (by decide) rfl rfl (by decide) (by decide)
      rfl rfl (by decide) (by decide)
  have hbo : ∀ k, ev (single 0 false) champ1 k = true := by
    intro k; rw [ev_eq, hlab]; simp [seqv, evq, single, Nat.mod_one]
  have hI : ∀ k, IsInterval (ev (single 0 false) champ1) k (k + 1) :=
    fun k => ⟨by omega, hbo k, hbo (k + 1), fun _ h1 h2 => by omega⟩
  have hv : ∀ k, value (ev B champ1) k (k + 1) = 0 := by
    intro k; simp [value, count]
  refine ⟨0, 1, hI 0, fun N => ⟨N, N + 1, Nat.le_refl _, hI N, by rw [hv, hv]⟩, rfl, ?_⟩
  intro i' j' hI' _
  have := hI'.lt
  omega

/-! ## two states -/

theorem good2 (M : Machine 2) : Good M 18 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := exists_codes2 M
  obtain ⟨cs, h⟩ := exists_chunk2 a b ha hb
  exact good_of_chunk h hc hd holdouts_good

/-! ## the three models -/

theorem bbbb1_anySets : IsBBBB 0 anySets 2 :=
  ⟨fun M B O s _ h => good1 M B O s h, champ1, fun _ _ => false, single 0 false, trivial,
    champ1_qq _⟩

theorem bbbb1_oneEach : IsBBBB 0 oneEach 2 :=
  ⟨fun M B O s _ h => good1 M B O s h, champ1, single 0 true, single 0 false,
    ⟨0, true, 0, false, fun _ _ => rfl, fun _ _ => rfl⟩, champ1_qq _⟩

theorem bbbb1_oneBoopRestBeep : IsBBBB 0 oneBoopRestBeep 2 :=
  ⟨fun M B O s _ h => good1 M B O s h, champ1, fun q b => !(q == 0 && b == false),
    single 0 false, ⟨0, false, fun _ _ => rfl, fun _ _ => rfl⟩, champ1_qq _⟩

theorem bbbb2_anySets : IsBBBB 1 anySets 18 :=
  ⟨fun M B O s _ h => good2 M B O s h, champ, single 0 false, single 0 true, trivial,
    champ_qq _ (by rw [champ_value, champ_value]; decide)⟩

theorem bbbb2_oneEach : IsBBBB 1 oneEach 18 :=
  ⟨fun M B O s _ h => good2 M B O s h, champ, single 0 false, single 0 true,
    ⟨0, false, 0, true, fun _ _ => rfl, fun _ _ => rfl⟩,
    champ_qq _ (by rw [champ_value, champ_value]; decide)⟩

theorem bbbb2_oneBoopRestBeep : IsBBBB 1 oneBoopRestBeep 18 :=
  ⟨fun M B O s _ h => good2 M B O s h, champ, fun q b => !(q == 0 && b == true),
    single 0 true, ⟨0, true, fun _ _ => rfl, fun _ _ => rfl⟩,
    champ_qq _ (by rw [champ_value, champ_value]; decide)⟩

end Bbbb
