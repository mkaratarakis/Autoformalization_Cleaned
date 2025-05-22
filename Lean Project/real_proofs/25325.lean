import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), (x || y) = (y || x) := by
  decide