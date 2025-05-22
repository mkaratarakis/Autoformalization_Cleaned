import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c t : Bool), cond c t false = ( c && t) := by
  decide