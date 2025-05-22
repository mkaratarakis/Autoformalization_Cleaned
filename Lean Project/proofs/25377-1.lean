import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by
  intros a b
  cases a <;> cases b <;> constructor <;> rfl

/- ACTUAL PROOF OF Bool.coe_false_iff_false -/

example : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by
  decide