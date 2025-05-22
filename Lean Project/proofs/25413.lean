import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  by_cases hb : b
  · simp [hb]
  · simp [hb]

/- ACTUAL PROOF OF Bool.cond_eq_ite -/

example {α} (b : Bool) (t e : α) : cond b t e = if b then t else e := by
  cases b <;> simp