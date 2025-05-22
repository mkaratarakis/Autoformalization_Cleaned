import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x < y → y < z → x < z := by
  intros x y z h1 h2
  cases x <;> cases y <;> cases z <;> cases h1 <;> cases h2
  all_goals {
    repeat contradiction
  }

/- ACTUAL PROOF OF Bool.lt_trans -/

example : ∀ {x y z : Bool}, x < y → y < z → x < z := by
  decide