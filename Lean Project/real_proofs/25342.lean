import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  decide