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
    · rw [eq_false_or_eq_true b]
      exact Or.inr rfl

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide