import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (p : Prop) [h : Decidable p] (a : Bool) (x y u v : α) :
  (ite p x y = cond a u v) ↔ ite p x y = ite a u v := by
  simp [Bool.cond_eq_ite]