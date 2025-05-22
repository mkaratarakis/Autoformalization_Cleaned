import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  by_cases hp : p
  · -- Case 1: p is true
    simp [hp]
    exact rfl
  · -- Case 2: p is false
    simp [hp]
    exact rfl

/- ACTUAL PROOF OF Bool.ite_eq_false_distrib -/

example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  cases h with | _ p => simp [p]