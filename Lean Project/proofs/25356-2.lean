import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≤ y := by
  intro x
  intro y
  intro h
  cases x <;> cases y <;> try rfl

/- ACTUAL PROOF OF Bool.le_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≤ y := by
  decide