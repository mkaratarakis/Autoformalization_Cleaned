import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b || true) = true := by
  cases b
  case false =>
    simp [bor]
  case true =>
    simp [bor]

/- ACTUAL PROOF OF Bool.or_true -/

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl