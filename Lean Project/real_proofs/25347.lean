import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by
  decide