import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≠ y := by
  intro x y h
  cases x
  · cases y
    · exfalso
      exact h
    · simp
  · cases y
    · simp
    · exfalso
      exact h

/- ACTUAL PROOF OF Bool.ne_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≠ y := by
  decide