import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  intro b
  constructor
  · intro h
    rw [h]
    exact false_ne_true
  · intro h
    by_cases hb : b = true
    · contradiction
    · exact eq_false_of_ne_true_of_ne_false h hb

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide