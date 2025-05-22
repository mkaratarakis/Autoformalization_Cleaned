import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  cases h with
  | isTrue hp =>
    simp [hp]
    exact rfl
  | isFalse hp =>
    simp [hp]
    exact rfl

/- ACTUAL PROOF OF Bool.ite_eq_true_distrib -/

example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  cases h with | _ p => simp [p]