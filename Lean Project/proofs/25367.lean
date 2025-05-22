import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), xor x y = xor y x := by
intro x
cases x
· intro y
  cases y
  · exact rfl
  · exact rfl
· intro y
  cases y
  · exact rfl
  · exact rfl

/- ACTUAL PROOF OF Bool.xor_comm -/

example : ∀ (x y : Bool), xor x y = xor y x := by
  decide