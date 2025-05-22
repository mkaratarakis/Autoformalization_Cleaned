import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀ (x : Bool), xor x x = false := by
  decide