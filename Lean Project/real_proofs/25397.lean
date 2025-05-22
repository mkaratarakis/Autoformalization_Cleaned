import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c f : Bool), cond c true f  = ( c || f) := by
  decide