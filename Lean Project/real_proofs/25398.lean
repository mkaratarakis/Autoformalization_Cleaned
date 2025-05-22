import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c t f : Bool),
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by
  decide