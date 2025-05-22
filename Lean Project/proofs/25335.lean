import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x ≠ y → x = !y := by
  intros x y h
  cases x
  · cases y
    · exact absurd rfl h
    · rfl
  · cases y
    · rfl
    · exact absurd rfl h

/- ACTUAL PROOF OF Bool.eq_not_of_ne -/

example : ∀ {x y : Bool}, x ≠ y → x = !y := by
  decide