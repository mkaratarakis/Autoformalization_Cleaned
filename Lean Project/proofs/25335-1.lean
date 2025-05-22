import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x ≠ y → x = !y := by
  intros x y h
  fin_cases x
  · intros
    fin_cases y
    · contradiction
    · rfl
  · intros
    fin_cases y
    · contradiction
    · rfl

/- ACTUAL PROOF OF Bool.eq_not_of_ne -/

example : ∀ {x y : Bool}, x ≠ y → x = !y := by
  decide