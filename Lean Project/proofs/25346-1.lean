import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), xor x x = false := by
  intro x
  cases x
  . apply xor_true_true
  . apply xor_false_false

/- ACTUAL PROOF OF Bool.xor_self -/

example : ∀ (x : Bool), xor x x = false := by
  decide