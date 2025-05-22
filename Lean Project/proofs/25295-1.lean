import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
intro a b
apply Iff.intro
  · intro h
    cases a <;> simp at h
    · exact h
    · contradiction
  · intro h
    cases a <;> simp
    · exact h
    · simp

/- ACTUAL PROOF OF Bool.and_iff_left_iff_imp -/

example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
  decide