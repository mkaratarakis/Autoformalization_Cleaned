import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (c : Bool) (t : α) : cond c t t = t := by
  cases c
  · simp
  · simp

/- ACTUAL PROOF OF Bool.cond_self -/

example (c : Bool) (t : α) : cond c t t = t := by
  cases c <;> rfl