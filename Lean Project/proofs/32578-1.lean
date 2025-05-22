import Init.Core
import Init.SimpLemmas




example : (p ↔ p ∧ q) ↔ (p → q) := by
  apply Iff.intro
  · intro h
    apply Iff.mp h
    intro p
    exact Iff.mpr h
  · intro h
    apply Iff.intro
    · intro hp
      apply And.intro
      · exact hp
      · exact h hp
    · intro hpq
      exact hpq.left

/- ACTUAL PROOF OF iff_self_and -/

example : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]