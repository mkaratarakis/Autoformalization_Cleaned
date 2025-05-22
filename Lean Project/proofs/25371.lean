import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x && xor y z) = xor (x && y) (x && z) := by
  intro x y z
  cases x <;> cases y <;> cases z
  all_goals {
    unfold xor
    unfold and
    repeat rfl
  }

/- ACTUAL PROOF OF Bool.and_xor_distrib_left -/

example : ∀ (x y z : Bool), (x && xor y z) = xor (x && y) (x && z) := by
  decide