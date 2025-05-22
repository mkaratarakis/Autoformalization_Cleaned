import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  constructor
  · intro h
    by_cases hb : b = true
    · exact hb
    · have : b = false := by
        apply bool.eq_false_of_ne_true
        exact hb
      contradiction
  · intro h
    rw [h]
    exact bool.true_ne_false

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide