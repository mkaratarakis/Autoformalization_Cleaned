import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y z : Bool}, x ≤ y → y < z → x < z := by
  intros x y z h1 h2
  cases x
  case false =>
    cases y
    case false =>
      exfalso
      apply h2
    case true =>
      apply h2
  case true =>
    cases y
    case false =>
      exfalso
      apply h1
    case true =>
      exfalso
      apply h2

/- ACTUAL PROOF OF Bool.lt_of_le_of_lt -/

example : ∀ {x y z : Bool}, x ≤ y → y < z → x < z := by
  decide