import Init.Core
import Init.SimpLemmas

open Bool


example : (!false) = true := by
  rfl

/- ACTUAL PROOF OF Bool.not_false -/

example : (!false) = true := by
  decide