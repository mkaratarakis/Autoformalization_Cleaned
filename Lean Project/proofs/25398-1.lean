import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c t f : Bool),
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by
  intros c t f
  cases c <;> simp [cond]
  · simp [ite]
  · simp [ite]

/- ACTUAL PROOF OF Bool.cond_eq_false_distrib -/

example : ∀(c t f : Bool),
    (cond c t f = false) = ite (c = true) (t = false) (f = false) := by
  decide