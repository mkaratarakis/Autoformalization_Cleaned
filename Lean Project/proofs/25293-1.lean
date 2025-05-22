import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x || !x) = true := by
  intro x
  cases x
  . apply or_true
  . apply or_false_iff.mpr
    rfl

/- ACTUAL PROOF OF Bool.or_not_self -/

example : ∀ (x : Bool), (x || !x) = true := by
  decide