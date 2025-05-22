import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  intro x
  cases x <;> intro y <;> cases y
  · exact Iff.intro (by simp) (by simp)
  · exact Iff.intro (by simp) (by simp)
  · exact Iff.intro (by simp) (by simp)
  · exact Iff.intro (by simp) (by simp)

/- ACTUAL PROOF OF Bool.lt_iff_le_not_le -/

example : ∀ {x y : Bool}, x < y ↔ x ≤ y ∧ ¬ y ≤ x := by
  decide