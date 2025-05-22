import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (a : Bool) (p : Prop) [h : Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  constructor
  · intro h1
    unfold cond ite at h1 ⊢
    unfold ite at h1
    rw [dite_eq_ite]
    rw [dite_eq_ite] at h1
    rw [h1]
    rfl
  · intro h1
    unfold cond ite
    unfold ite at h1
    rw [dite_eq_ite]
    rw [dite_eq_ite] at h1
    rw [h1]
    rfl

/- ACTUAL PROOF OF Bool.cond_eq_ite_iff -/

example (a : Bool) (p : Prop) [h : Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]