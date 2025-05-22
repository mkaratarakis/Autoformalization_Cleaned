import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (a : Bool) (x y u v : α) :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  constructor
  · intro h1
    rw [h1]
    exact ite_eq_cond _ _ _
  · intro h1
    rw [← h1]
    exact cond_eq_ite _ _ _

/- ACTUAL PROOF OF Bool.ite_eq_cond_iff -/

example (p : Prop) [h : Decidable p] (a : Bool) (x y u v : α) :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  simp [Bool.cond_eq_ite]