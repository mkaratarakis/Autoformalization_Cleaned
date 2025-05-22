import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (t : Bool) :
    (ite p t false) = (p && t) := by
  cases h with | _ p => simp [p]