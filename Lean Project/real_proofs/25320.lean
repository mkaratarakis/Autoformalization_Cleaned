import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀b, (false == b) = !b := by
  decide