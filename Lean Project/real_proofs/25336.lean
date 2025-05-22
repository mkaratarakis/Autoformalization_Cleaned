import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by
  decide