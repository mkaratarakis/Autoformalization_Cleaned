import Init.Core
import Init.SimpLemmas




example : (¬ True) = False := by
  change (True → False) = False
  apply propext
  apply not_true

/- ACTUAL PROOF OF not_true_eq_false -/

example : (¬ True) = False := by
  decide