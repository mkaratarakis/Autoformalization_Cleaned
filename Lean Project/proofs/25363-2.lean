import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
intro x y z h1 h2
cases x <;> cases y <;> cases z <;> simp * at *
case tt tt tt => exact decTrivial
case ff ff ff => exact decTrivial
case tt ff tt => exact decTrivial
case tt ff ff => exact decTrivial
case ff tt tt => exact h1
case ff tt ff => exact h1
case ff ff tt => exact (h2.trans h1)
case tt tt ff => exact decTrivial

/- ACTUAL PROOF OF Bool.lt_of_lt_of_le -/

example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
  decide