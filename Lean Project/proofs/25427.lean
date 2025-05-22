import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> rfl

/- ACTUAL PROOF OF Bool.apply_cond -/

example (f : α → β) {b : Bool} {a a' : α} :
    f (bif b then a else a') = bif b then f a else f a' := by
  cases b <;> simp