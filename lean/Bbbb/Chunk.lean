import Bbbb.Certs1
import Bbbb.Certs2

namespace Bbbb

/-- every machine `ofCodes2 a b c d` of the chunk has a valid certificate or is a holdout -/
def chunkOK2 (a b : Nat) (cs : List Cert) : Bool :=
  (List.range 81).all (fun i => checkCert (ofCodes2 a b (i / 9) (i % 9)) 18 (cs.getD i .holdout) ||
    decide ((a, b, i / 9, i % 9) ∈ holdouts2))

end Bbbb

namespace Bbbb

theorem good_of_chunk {a b c d : Nat} {cs : List Cert} (h : chunkOK2 a b cs = true)
    (hc : c < 9) (hd : d < 9)
    (hh : ∀ a b c d, (a, b, c, d) ∈ holdouts2 → Good (ofCodes2 a b c d) 18) :
    Good (ofCodes2 a b c d) 18 := by
  unfold chunkOK2 at h
  rw [List.all_eq_true] at h
  have h' := h (9 * c + d) (List.mem_range.2 (by omega))
  rw [show (9 * c + d) / 9 = c by omega, show (9 * c + d) % 9 = d by omega,
    Bool.or_eq_true, decide_eq_true_eq] at h'
  rcases h' with h' | h'
  · exact checkCert_sound h'
  · exact hh a b c d h'

end Bbbb
