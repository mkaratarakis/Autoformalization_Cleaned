import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : (false = b) = (b = false) := by
cases b
case false => rfl
case true =>
  have : (false = true) = false := rfl
  have : (true = false) = false := by simp [false_ne_true]
  show (false = true) = (true = false)
  exact this

/- ACTUAL PROOF OF Bool.false_eq -/

example (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp