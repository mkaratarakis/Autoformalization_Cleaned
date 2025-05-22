import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by
  cases h with
  | isTrue hp =>
    show ite true t true = (!(decide true) || t)
    rw [dite_true_iff]
    rw [decide_eq_true_iff]
    rw [not_true_eq_false]
    rw [false_or]
  | isFalse hp =>
    show ite false t true = (!(decide false) || t)
    rw [dite_false_iff]
    rw [decide_eq_false_iff]
    rw [not_false_eq_true]
    rw [true_or]

/- ACTUAL PROOF OF Bool.if_true_right -/

example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t true) = (!(p : Bool) || t) := by
  cases h with | _ p => simp [p]