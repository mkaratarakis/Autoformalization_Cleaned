import Init.BinderPredicates
import Init.Data.Bool

open Bool



example : ∀(c t f : Bool),
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  decide