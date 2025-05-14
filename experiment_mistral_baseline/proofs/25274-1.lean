import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    rw [h]
    exact ne_of_eq_of_ne rfl true_ne_false
  · intro h
    cases b <;> simp [*]

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide