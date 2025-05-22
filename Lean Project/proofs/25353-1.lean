import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  intros a b
  cases a <;> cases b
  all_goals
    repeat (first | apply Bool.noConfusion)
    rfl

/- ACTUAL PROOF OF Bool.not_eq_not -/

example : ∀ {a b : Bool}, ¬a = !b ↔ a = b := by
  decide