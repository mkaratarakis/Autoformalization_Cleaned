import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by
  decide