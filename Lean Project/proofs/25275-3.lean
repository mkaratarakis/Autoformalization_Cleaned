import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  apply Iff.intro
  · intro h
    cases b <;> simp [*] at *
  · intro h
    rw [h]
    exact true_ne_false

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide