import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), (x != z) = (y != z) ↔ x = y := by
  decide