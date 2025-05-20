import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  constructor
  · intro h
    by_cases hb : b = true
    · exact hb
    · have : b = false := by simpa [hb] using @eq_false_or_eq_true b
      contradiction
  · intro h
    rw [h]
    exact Bool.false_ne_true

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide