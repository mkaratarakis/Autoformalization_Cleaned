import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(b : Bool), (false != b) =  b := by
  decide