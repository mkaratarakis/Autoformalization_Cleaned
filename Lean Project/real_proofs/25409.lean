import Init.BinderPredicates
import Init.Data.Bool

open Bool



example (b : Bool) (t e : α) : cond (!b) t e = cond b e t := by
  cases b <;> rfl