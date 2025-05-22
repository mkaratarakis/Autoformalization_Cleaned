import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), xor x x = false := by
  intro x
  cases x
  . simp [xor]
  . simp [xor]

/- ACTUAL PROOF OF Bool.xor_self -/

example : ∀ (x : Bool), xor x x = false := by
  decide