import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by
  intros x y z
  cases x <;> cases y <;> cases z <;> simp

/- ACTUAL PROOF OF Bool.bne_left_inj -/

example : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by
  decide