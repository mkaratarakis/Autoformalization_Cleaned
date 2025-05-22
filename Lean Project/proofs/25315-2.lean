import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by
  intro x y
  apply Iff.intro
  . intro h
    cases x <;> simp [*] at *
    exact Or.inl h
    exact Or.inr h
  . rintro (h|h) <;> simp [*]

/- ACTUAL PROOF OF Bool.or_eq_true_iff -/

example : ∀ (x y : Bool), (x || y) = true ↔ x = true ∨ y = true := by
  simp