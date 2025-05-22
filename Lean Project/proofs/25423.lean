import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c b : Bool), cond c b c = (c && b) := by
intro c b
unfold cond
unfold and
split <;> simp [*]

/- ACTUAL PROOF OF Bool.cond_false_same -/

example : ∀(c b : Bool), cond c b c = (c && b) := by
  decide