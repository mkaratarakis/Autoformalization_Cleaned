import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≠ y := by
  intro x y h
  cases x
  · cases y
    · exact absurd h (not_lt_of_le (le_of_lt h))
    · simp at h
  · cases y
    · simp at h
    · exact absurd h (not_lt_of_le (le_of_lt h))

/- ACTUAL PROOF OF Bool.ne_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≠ y := by
  decide