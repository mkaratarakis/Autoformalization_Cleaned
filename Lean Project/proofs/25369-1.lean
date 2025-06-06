import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x = y → x ≤ y := by
  intros x y h
  cases h
  case refl =>
    exact le_refl

/- ACTUAL PROOF OF Bool.le_of_eq -/

example : ∀ {x y : Bool}, x = y → x ≤ y := by
  decide