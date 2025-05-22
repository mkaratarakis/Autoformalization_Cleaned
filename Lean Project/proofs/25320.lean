import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀b, (false == b) = !b := by
  intros b
  cases b
  case true =>
    rfl
  case false =>
    rfl

/- ACTUAL PROOF OF Bool.false_beq -/

example : ∀b, (false == b) = !b := by
  decide