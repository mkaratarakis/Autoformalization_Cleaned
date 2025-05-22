import Init.BinderPredicates
import Init.Data.Bool

open Bool

example : ∀ {x y : Bool}, x < y ∨ x = y → x ≤ y := by
  intro x y h
  cases h
  . exact Or.inl h
  . exact Or.inr h

/- ACTUAL PROOF OF Bool.le_of_lt_or_eq -/

example : ∀ {x y : Bool}, x < y ∨ x = y → x ≤ y := by
  decide