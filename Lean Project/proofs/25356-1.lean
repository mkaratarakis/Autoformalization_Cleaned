import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≤ y := by
  intro x
  intro y
  intro h
  exact le_of_lt h

/- ACTUAL PROOF OF Bool.le_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≤ y := by
  decide