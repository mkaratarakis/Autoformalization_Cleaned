import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b = false ↔ b ≠ true := by
  intro b
  constructor
  · intro h
    exact Ne.symm (Ne.ofEqFun h)
  · intro h
    cases b <;> simp [*] at h

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide