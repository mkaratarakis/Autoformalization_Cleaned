import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
intro x y z h1 h2
cases x <;> cases y <;> cases z
· exact (False.not_lt_false h1)
· exact (False.not_lt_false h1)
· exact (False.not_lt_false h1)
· exact (False.not_lt_false h1)
· exact h1
· exact h1
· exact (False.not_lt_false h1)
· exact (False.not_lt_false h1)

/- ACTUAL PROOF OF Bool.lt_of_lt_of_le -/

example : ∀ {x y z : Bool}, x < y → y ≤ z → x < z := by
  decide