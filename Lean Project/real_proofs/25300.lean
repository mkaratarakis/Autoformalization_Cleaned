import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {a b : Bool} : a = b ↔ (a ↔ b) := by
  cases b <;> simp