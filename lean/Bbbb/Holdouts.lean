import Bbbb.Certs2

/-! # The 12 holdouts (6 machines and their mirror images) -/

namespace Bbbb

theorem holdouts_good : ∀ a b c d, (a, b, c, d) ∈ holdouts2 → Good (ofCodes2 a b c d) 18 := by
  sorry

end Bbbb
