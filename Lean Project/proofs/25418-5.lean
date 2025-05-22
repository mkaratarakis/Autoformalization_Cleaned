import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  by_cases hp : p
  · -- Case 1: p is true
    simp [hp]
    exact Iff.intro (by simp) (by simp)
  · -- Case 2: p is false
    simp [hp]
    exact Iff.intro (by simp) (by simp)

/- ACTUAL PROOF OF Bool.not_ite_eq_false_eq_false -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  cases h with | _ p => simp [p]