import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    rw [h]
    exact ne_of_eq_of_ne rfl (by simp)
  · intro h
    rw [eq_false_iff_not_eq_true]
    exact h

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide