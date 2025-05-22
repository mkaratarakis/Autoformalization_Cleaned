import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  by_cases hp : p
  · have : decide p = true := by simp [hp]
    simp [this]
    exact Bool.and_true (decide q)
  · have : decide p = false := by simp [hp]
    simp [this]
    exact Bool.and_false (decide q)

/- ACTUAL PROOF OF Bool.decide_and -/

example (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  cases dp with | _ p => simp [p]