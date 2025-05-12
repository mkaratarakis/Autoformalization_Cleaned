import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  intro a b
  apply Iff.intro
  . intro h
    cases b <;> simp [and, h]
    . exact h_1
    . exact (iff_of_true (propext h_1)).mpr
  . intro h
    cases b <;> simp [and]
    . exact (h trivial).elim
    . exact (iff_of_false (propext h_1)).mpr

/- ACTUAL PROOF OF Bool.and_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a && b) = b) ↔ (b → a) := by
  decide