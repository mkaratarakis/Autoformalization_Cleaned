import Init.BinderPredicates
import Init.Data.Bool

open Bool

example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  intros x y hlt
  cases x <;> cases y <;> try cases hlt
  case false.true.refl =>
  apply not_lt_of_ge
  simp

/- ACTUAL PROOF OF Bool.lt_asymm -/

example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  decide