import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x && (y && z)) = (y && (x && z)) := by
  intros x y z
  cases x <;> cases y <;> cases z
  all_goals {
    simp [and]
  }

/- ACTUAL PROOF OF Bool.and_left_comm -/

example : ∀ (x y z : Bool), (x && (y && z)) = (y && (x && z)) := by
  decide