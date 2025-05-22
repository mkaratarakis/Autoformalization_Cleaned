import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≠ y := by
  intro x y h
  cases x
  · cases y
    · exact False.not_lt_false h
    · simp
  · cases y
    · simp
    · exact False.not_lt_true h

/- ACTUAL PROOF OF Bool.ne_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≠ y := by
  decide