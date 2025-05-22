import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (b = false ∧ b = true) ↔ False := by
  intro b
  apply Iff.intro
  . intro h
    cases h
    contradiction
  . intro h
    exfalso
    exact h

/- ACTUAL PROOF OF Bool.eq_false_and_eq_true_self -/

example : ∀(b : Bool), (b = false ∧ b = true) ↔ False := by
  decide