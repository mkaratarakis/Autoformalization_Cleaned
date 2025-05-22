import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), xor x y = xor y x := by
  decide