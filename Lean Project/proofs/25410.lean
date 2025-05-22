import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  by_cases hp : p
  · -- Case 1: p is true
    have h₁ : ite p (b = true) (c = false) = (b = true) := by simp [hp]
    have h₂ : ite p (b = false) (c = true) = (b = false) := by simp [hp]
    simp [hp, h₁, h₂]
  · -- Case 2: p is false
    have h₁ : ite p (b = true) (c = false) = (c = false) := by simp [hp]
    have h₂ : ite p (b = false) (c = true) = (c = true) := by simp [hp]
    simp [hp, h₁, h₂]

/- ACTUAL PROOF OF Bool.not_ite_eq_true_eq_false -/

example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  cases h with | _ p => simp [p]