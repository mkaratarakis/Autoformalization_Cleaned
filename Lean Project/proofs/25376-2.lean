import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y ∨ x = y → x ≤ y := by
  intro x y h
  cases h
  . left
    exact h
  . right
    exact h

/- ACTUAL PROOF OF Bool.le_of_lt_or_eq -/

example : ∀ {x y : Bool}, x < y ∨ x = y → x ≤ y := by
  decide