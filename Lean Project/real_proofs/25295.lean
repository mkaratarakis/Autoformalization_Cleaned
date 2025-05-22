import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
  decide