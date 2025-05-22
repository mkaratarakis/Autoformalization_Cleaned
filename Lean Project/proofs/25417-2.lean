import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
cases h
· intro hnp
  by_cases hp : p
  · rw [if_pos hp] at hnp
    rw [if_pos hp]
    apply not_eq_true_eq_false.mp
    assumption
  · rw [if_neg hp] at hnp
    rw [if_neg hp]
    apply not_eq_true_eq_false.mp
    assumption
· intro hnp
  by_cases hp : p
  · rw [if_pos hp] at hnp
    rw [if_pos hp]
    apply not_eq_false_eq_true.mpr
    assumption
  · rw [if_neg hp] at hnp
    rw [if_neg hp]
    apply not_eq_false_eq_true.mpr
    assumption

/- ACTUAL PROOF OF Bool.not_ite_eq_true_eq_true -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]