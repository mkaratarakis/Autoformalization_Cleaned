import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp