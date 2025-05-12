import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : {b : Bool} → b ≠ false ↔ b = true := by
  apply Iff.intro
  · intro h
    cases b <;> simp
    exact h
  · intro h
    rw [h]
    exact false_ne_true

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide