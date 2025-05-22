import Init.Core
import Init.SimpLemmas




example : (¬ True) = False := by
  apply (not_false_eq_true False).symm
  simp

/- ACTUAL PROOF OF not_true_eq_false -/

example : (¬ True) = False := by
  decide