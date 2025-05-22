import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (c : Bool) (t : α) : cond c t t = t := by
  cases c <;> rfl