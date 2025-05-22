import Init.BinderPredicates
import Init.Data.Bool

open Bool

example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  intros x y hlt
  cases x <;> cases y <;> try cases hlt
  case false.false => exact absurd rfl hlt
  case false.true => exact absurd (lt_irrefl true) rfl
  case true.false => exact absurd (lt_irrefl false) rfl
  case true.true => exact absurd rfl hlt

/- ACTUAL PROOF OF Bool.lt_asymm -/

example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  decide