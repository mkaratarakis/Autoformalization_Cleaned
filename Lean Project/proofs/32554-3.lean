import Init.Core
import Init.SimpLemmas




example : (¬ True) = False := by
  change (True → False) = False
  rfl

/- ACTUAL PROOF OF not_true_eq_false -/

example : (¬ True) = False := by
  decide