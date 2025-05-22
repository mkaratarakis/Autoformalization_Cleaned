import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), (x && xor y z) = xor (x && y) (x && z) := by
  decide