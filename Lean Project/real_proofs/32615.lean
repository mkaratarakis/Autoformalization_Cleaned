import Init.Core
import Init.SimpLemmas

open Bool



example (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide