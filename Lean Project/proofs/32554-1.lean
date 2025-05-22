import Init.Core
import Init.SimpLemmas




example : (¬ True) = False := by
  rfl

/- ACTUAL PROOF OF not_true_eq_false -/

example : (¬ True) = False := by
  decide