import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(a b : Bool), (a != (a != b)) = b := by
  decide