import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by
  decide