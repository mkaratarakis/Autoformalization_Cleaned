import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
intro x y z h1 h2
cases x <;> cases y <;> cases z
· exact decTrivial
· exact decTrivial
· exact decTrivial
· exact decTrivial
· exact h1
· exact h1
· exact h1
· exact decTrivial

/- ACTUAL PROOF OF Bool.lt_of_lt_of_le -/

example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
  decide