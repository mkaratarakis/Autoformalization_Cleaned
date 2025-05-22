import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by
  simp