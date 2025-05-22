import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  intro b
  constructor
  · intro h
    rw [h]
    exact Ne.symm (Ne.symm (ne_of_ne_of_eq (by simp) rfl))
  · intro h
    by_cases hb : b = true
    · exfalso
      exact h hb
    · exact eq_false_of_ne_true hb

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide