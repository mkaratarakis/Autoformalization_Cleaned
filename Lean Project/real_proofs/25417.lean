import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (b c : Bool) :
  ¬(ite p (b = true) (c = true)) ↔ (ite p (b = false) (c = false)) := by
  cases h with | _ p => simp [p]