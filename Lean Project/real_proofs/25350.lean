import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by
  decide