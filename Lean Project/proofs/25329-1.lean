import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by
  intros x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> rfl

/- ACTUAL PROOF OF Bool.bne_assoc -/

example : ∀ (x y z : Bool), ((x != y) != z) = (x != (y != z)) := by
  decide