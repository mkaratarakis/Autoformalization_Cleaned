import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by
  decide