import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c b : Bool), cond c c b = (c || b) := by
  decide