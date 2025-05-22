import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (b : Bool) : b.toNat = 0 ↔ b = false := by
  cases b <;> simp