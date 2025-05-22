import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∨ q) = (p || q) := by
  cases hp : decide p
  · -- Case 1: decide p is true
    simp [hp, Bool.bor_true]
  · -- Case 2: decide p is false
    simp [hp]
    cases hq : decide q
    · simp [hq]
    · simp [hq]

/- ACTUAL PROOF OF Bool.decide_or -/

example (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∨ q) = (p || q) := by
  cases dp with | _ p => simp [p]