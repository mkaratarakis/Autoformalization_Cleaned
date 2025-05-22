import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  decide