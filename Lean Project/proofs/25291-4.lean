import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b
  · exact Decidable.rec (fun h => false) (fun h => true) (isFalse inst✝)
  · exact Decidable.rec (fun h => false) (fun h => true) (isTrue inst✝)

/- ACTUAL PROOF OF Bool.decide_eq_true -/

example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp