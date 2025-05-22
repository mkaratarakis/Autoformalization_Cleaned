import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ {x y : Bool}, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  cases x <;> cases y <;> try rfl
  case false.false => assumption
  all_goals {
    apply False.elim
    apply hyx
    assumption
  }

/- ACTUAL PROOF OF Bool.le_antisymm -/

example : ∀ {x y : Bool}, x ≤ y → y ≤ x → x = y := by
  decide