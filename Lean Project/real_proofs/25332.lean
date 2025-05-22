import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), (x && y) = false ↔ (x = true → y = false) := by
  decide