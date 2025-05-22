import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p q : Prop) [dpq : Decidable (p ∧ q)] [dp : Decidable p] [dq : Decidable q] :
    decide (p ∧ q) = (p && q) := by
  cases dp with | _ p => simp [p]