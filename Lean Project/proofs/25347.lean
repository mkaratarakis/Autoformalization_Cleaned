import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by
  intros a b
  cases a
  · -- Case 1: a = true
    cases b
    · -- Subcase 1.1: b = false
      simp [iff_true_left]
    · -- Subcase 1.2: b = true
      simp [iff_false_left]
  · -- Case 2: a = false
    cases b
    · -- Subcase 2.1: b = false
      simp [iff_false_left]
    · -- Subcase 2.2: b = true
      simp [iff_false_left]

/- ACTUAL PROOF OF Bool.coe_true_iff_false -/

example : ∀(a b : Bool), (a ↔ b = false) ↔ a = (!b) := by
  decide