import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
apply decidable_of_iff_decidable _ h
split
· intro hnp
  by_cases hp : p
  · rw [ite_true hp] at hnp
    rw [ite_true hp]
    apply not_eq_true_eq_false.mp
    assumption
  · rw [ite_false hp] at hnp
    rw [ite_false hp]
    apply not_eq_true_eq_false.mp
    assumption
· intro hnp
  by_cases hp : p
  · rw [ite_true hp] at hnp
    rw [ite_true hp]
    apply not_eq_false_eq_true.mpr
    assumption
  · rw [ite_false hp] at hnp
    rw [ite_false hp]
    apply not_eq_false_eq_true.mpr
    assumption

/- ACTUAL PROOF OF Bool.not_ite_eq_true_eq_true -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]