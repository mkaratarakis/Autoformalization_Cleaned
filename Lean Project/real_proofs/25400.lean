import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {b : Bool} {a a' : α} (h : b = false) : (bif b then a else a') = a' := by
  rw [h, cond_false]