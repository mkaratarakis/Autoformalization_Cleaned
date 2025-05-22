import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x != z) = (y != z) ↔ x = y := by
  intros x y z
  cases x <;> cases y <;> cases z <;> simp [*]

/- ACTUAL PROOF OF Bool.bne_right_inj -/

example : ∀ (x y z : Bool), (x != z) = (y != z) ↔ x = y := by
  decide