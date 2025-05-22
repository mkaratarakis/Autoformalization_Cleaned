import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
cases h
· constructor
  · intro hnp
    rw [ite_false h]
    rw [not_eq_true_eq_false] at hnp
    exact hnp
  · intro hnp
    rw [ite_false h]
    rw [not_eq_false_eq_true]
    exact hnp
· constructor
  · intro hnp
    rw [ite_true h]
    rw [not_eq_true_eq_false] at hnp
    exact hnp
  · intro hnp
    rw [ite_true h]
    rw [not_eq_false_eq_true]
    exact hnp

/- ACTUAL PROOF OF Bool.not_ite_eq_true_eq_true -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]