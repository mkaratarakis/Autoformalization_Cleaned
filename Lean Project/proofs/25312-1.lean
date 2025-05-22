import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  intros a b
  apply Iff.intro
  . intro h
    cases b <;> simp [and_eq_true, and_eq_false] at h
    . exact h
    . rintro rfl
      exact (h.symm ▸ and_eq_false)
  . intro h
    cases b <;> simp [and_eq_true, and_eq_false]
    . exact (h rfl)
    . simp [and_eq_false]

/- ACTUAL PROOF OF Bool.and_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  decide