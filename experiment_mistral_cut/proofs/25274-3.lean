import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    rw [h]
    exact false_ne_true
  · intro h
    by_cases hb : b = true
    · exfalso
      exact h hb
    · rw [← hb]
      exact rfl

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide