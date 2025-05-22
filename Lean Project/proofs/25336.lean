import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by
  intro x y
  cases x <;> cases y <;> simp [or_eq_true_iff]

/- ACTUAL PROOF OF Bool.or_eq_false_iff -/

example : ∀ (x y : Bool), (x || y) = false ↔ x = false ∧ y = false := by
  decide