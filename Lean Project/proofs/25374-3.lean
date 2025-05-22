import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  intro x
  cases x <;> intro y <;> cases y
  · simp [lt_eq_le_and_ne, le_eq_eq_or_le]
  · simp [lt_eq_le_and_ne, le_eq_eq_or_le]
  · simp [lt_eq_le_and_ne, le_eq_eq_or_le]
  · simp [lt_eq_le_and_ne, le_eq_eq_or_le]

/- ACTUAL PROOF OF Bool.lt_iff_le_not_le -/

example : ∀ {x y : Bool}, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  decide