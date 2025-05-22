import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (a : Bool) (p : Prop) [h : Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  constructor
  · intro h1
    cases a <;> simp at h1
    · exact h1
    · exact h1
  · intro h1
    cases a <;> simp
    · exact h1
    · exact h1

/- ACTUAL PROOF OF Bool.cond_eq_ite_iff -/

example (a : Bool) (p : Prop) [h : Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]