import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (t f : Bool) :
    (ite p t f = true) = ite p (t = true) (f = true) := by
  cases h with | _ p => simp [p]