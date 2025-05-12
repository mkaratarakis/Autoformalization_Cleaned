import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    rw [h]
    exact false_ne_true
  · intro h
    cases eq_false_or_eq_true b
    · contradiction
    · assumption

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide