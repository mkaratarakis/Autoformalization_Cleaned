import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b || true) = true := by
  cases b
  case false =>
    rfl
  case true =>
    rfl

/- ACTUAL PROOF OF Bool.or_true -/

example (b : Bool) : (b || true) = true := by
  cases b <;> rfl