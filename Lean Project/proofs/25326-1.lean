import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x   != !x) = true := by
  intro x
  decide

/- ACTUAL PROOF OF Bool.bne_not_self -/

example : ∀ (x : Bool), (x   != !x) = true := by
  decide