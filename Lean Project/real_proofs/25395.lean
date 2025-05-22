import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (a : Bool) (p : Prop) [h : Decidable p] (x y u v : α) :
  (cond a x y = ite p u v) ↔ ite a x y = ite p u v := by
  simp [Bool.cond_eq_ite]