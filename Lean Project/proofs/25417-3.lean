import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
cases h
· intro hp
  constructor
  · intro hnp
    apply if_neg hp
    rw [hnp]
    exact not_true_eq_false
  · intro hnp
    apply if_neg hp
    rw [hnp]
    exact not_false_eq_true
· intro hp
  constructor
  · intro hnp
    apply if_pos hp
    rw [hnp]
    exact not_true_eq_false
  · intro hnp
    apply if_pos hp
    rw [hnp]
    exact not_false_eq_true

/- ACTUAL PROOF OF Bool.not_ite_eq_true_eq_true -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]