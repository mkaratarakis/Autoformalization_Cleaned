import Init.Core
import Init.SimpLemmas





example : (p ↔ p ∧ q) ↔ (p → q) := by
  rw [@Iff.comm p, and_iff_left_iff_imp]