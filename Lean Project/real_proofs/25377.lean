import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by
  decide