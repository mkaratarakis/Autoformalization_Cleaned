import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∨ q) = (p || q) := by
  cases hp : decide p
  · -- Case 1: decide p is true
    have : decide (p ∨ q) = true
    exact Decidable.byCases ( fun h => by simp [hp, h] ) ( fun h => by simp [hp, h] )
    have : decide p || decide q = true
    simp [hp]
    exact rfl
  · -- Case 2: decide p is false
    have : decide (p ∨ q) = decide q
    exact Decidable.byCases ( fun h => by simp [hp, h] ) ( fun h => by simp [hp, h] )
    have : decide p || decide q = decide q
    simp [hp]
    exact rfl

/- ACTUAL PROOF OF Bool.decide_or -/

example (p q : Prop) [dpq : Decidable (p ∨ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∨ q) = (p || q) := by
  cases dp with | _ p => simp [p]