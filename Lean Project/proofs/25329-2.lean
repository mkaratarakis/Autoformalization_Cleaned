import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by
  intros x y z
  decide

/- ACTUAL PROOF OF Bool.bne_assoc -/

example : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by
  decide