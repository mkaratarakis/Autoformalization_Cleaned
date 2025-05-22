import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  intro a b
  apply Iff.intro
  . intro h
    cases a <;> simp [h]
  . intro h
    cases a <;> simp [h]

/- ACTUAL PROOF OF Bool.coe_false_iff_true -/

example : ∀(a b : Bool), (a = false ↔ b) ↔ (!a) = b := by
  decide