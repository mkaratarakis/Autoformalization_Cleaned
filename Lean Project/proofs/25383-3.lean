import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b:Bool), (b = false → b = true) ↔ (b = true) := by
intro b
apply Iff.intro
  . intro h
    rw [h]
    exact (iff_true_intro)
  . intro h
    rw [h]
    exact (iff_true_intro)

/- ACTUAL PROOF OF Bool.eq_false_imp_eq_true -/

example : ∀(b:Bool), (b = false → b = true) ↔ (b = true) := by
  decide