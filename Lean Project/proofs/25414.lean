import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c b : Bool), cond c c b = (c || b) := by
  intro c b
  cases c <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.cond_true_same -/

example : ∀(c b : Bool), cond c c b = (c || b) := by
  decide