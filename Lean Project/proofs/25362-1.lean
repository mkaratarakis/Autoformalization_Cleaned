import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  intros x y hlt
  cases x <;> cases y <;> try cases hlt
  repeat contradiction

/- ACTUAL PROOF OF Bool.lt_asymm -/

example : ∀ {x y : Bool}, x < y → ¬ y < x := by
  decide