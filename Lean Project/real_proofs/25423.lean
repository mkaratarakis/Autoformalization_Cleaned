import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c b : Bool), cond c b c = (c && b) := by
  decide