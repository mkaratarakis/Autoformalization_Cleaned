import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  cases h : decide p
  · simp [h]
  · simp [h]

/- ACTUAL PROOF OF Bool.cond_decide -/

example {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]