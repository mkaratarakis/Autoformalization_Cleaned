import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp