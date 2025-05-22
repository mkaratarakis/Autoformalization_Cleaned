import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  by_cases hp : p
  · have : decide p = true := by simp [hp]
    simp [this, and_true]
    exact Decidable.toBool_eq_true_iff.2 dq
  · have : decide p = false := by simp [hp]
    simp [this, and_false]
    exact Decidable.toBool_eq_false_iff.2 dp

/- ACTUAL PROOF OF Bool.decide_and -/

example (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  cases dp with | _ p => simp [p]