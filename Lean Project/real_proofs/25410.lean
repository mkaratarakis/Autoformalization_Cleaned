import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = false)) ↔ (ite p (b = false) (c = true)) := by
  cases h with | _ p => simp [p]