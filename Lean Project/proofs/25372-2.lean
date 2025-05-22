import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → x ≠ y := by
  intro x y h
  cases x
  · cases y
    · exact absurd h (not_lt_false false)
    · simp at h
  · cases y
    · simp at h
    · exact absurd h (not_lt_true true)

/- ACTUAL PROOF OF Bool.ne_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≠ y := by
  decide