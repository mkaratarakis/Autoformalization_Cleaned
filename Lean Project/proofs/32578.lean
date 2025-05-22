import Init.Core
import Init.SimpLemmas




example : (p ↔ p ∧ q) ↔ (p → q) := by
  apply Iff.intro
  · intro h
    intro p
    exact (Iff.mp h p).right
  · intro h
    apply Iff.intro
    · intro p
      exact ⟨p, h p⟩
    · intro hpq
      exact hpq.left

/- ACTUAL PROOF OF iff_self_and -/

example : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]