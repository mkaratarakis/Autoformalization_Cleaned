import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = false) = ite p (t = false) (f = false) := by
  cases h with | _ p => simp [p]