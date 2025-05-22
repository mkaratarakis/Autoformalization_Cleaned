import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  by_cases hp : p
  · -- Case 1: p is true
    simp [hp]
    apply Iff.intro
    · intro hnp
      apply hnp
      exact iff_of_eq rfl
    · intro hp
      apply hp
      exact iff_of_eq rfl
  · -- Case 2: p is false
    simp [hp]
    apply Iff.intro
    · intro hnp
      apply hnp
      exact iff_of_eq rfl
    · intro hp
      apply hp
      exact iff_of_eq rfl

/- ACTUAL PROOF OF Bool.not_ite_eq_false_eq_false -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = false) (c = false)) ↔ (ite p (b = true) (c = true)) := by
  cases h with | _ p => simp [p]