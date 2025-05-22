import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c t f : Bool),
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
intro c t f
by_cases h: c = true
. pos
  rw [h, cond_true]
  simp
. neg
  rw [cond_false]
  simp

/- ACTUAL PROOF OF Bool.cond_eq_true_distrib -/

example : ∀(c t f : Bool),
    (cond c t f = true) = ite (c = true) (t = true) (f = true) := by
  decide