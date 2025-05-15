import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  intros a b
  cases b
  · simp
  · cases a
    · simp
    · simp

/- ACTUAL PROOF OF Bool.and_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  decide