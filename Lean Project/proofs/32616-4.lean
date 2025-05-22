import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : ((!b) = false) = (b = true) := by
  cases b
  case false =>
    show (not false = false) = (false = true)
    rw [Bool.not_false]
    show (true = false) = (false = true)
    rfl
  case true =>
    show (not true = false) = (true = true)
    rw [Bool.not_true]
    show (false = false) = (true = true)
    rfl

/- ACTUAL PROOF OF Bool.not_eq_false' -/

example (b : Bool) : ((!b) = false) = (b = true) := by
  cases b <;> simp