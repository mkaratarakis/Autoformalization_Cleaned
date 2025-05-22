import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  cases h : decide p
  · show e = if p then t else e
    rw [dif_neg (by rwa [←isFalse_iff])]
    rfl
  · show t = if p then t else e
    rw [dif_pos (by rwa [←isTrue_iff])]
    rfl

/- ACTUAL PROOF OF Bool.cond_decide -/

example {α} (p : Prop) [Decidable p] (t e : α) :
    cond (decide p) t e = if p then t else e := by
  simp [cond_eq_ite]