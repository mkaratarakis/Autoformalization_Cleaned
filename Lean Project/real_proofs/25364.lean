import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x y : Bool), xor x (!y) = !(xor x y) := by
  decide