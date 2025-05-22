import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀b, (true  == b) =  b := by
  decide