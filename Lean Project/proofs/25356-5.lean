import Init.BinderPredicates
import Init.Data.Bool

open Bool

example : ∀ {x y : Bool}, x < y → x ≤ y := by
  intro x y h
  cases x <;> cases y <;> try exact isTrue (x ≤ y)
  · contradiction
  · exact rfl
  · contradiction
  · exact rfl

/- ACTUAL PROOF OF Bool.le_of_lt -/

example : ∀ {x y : Bool}, x < y → x ≤ y := by
  decide