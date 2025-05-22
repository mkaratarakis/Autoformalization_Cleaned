import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by
  intros a b
  cases a <;> cases b
  · constructor
    · intro h
      rfl
    · intro h
      rfl
  · constructor
    · intro h
      apply True.not_eq_false
    · intro h
      apply True.not_eq_false
  · constructor
    · intro h
      apply True.not_eq_false
    · intro h
      apply True.not_eq_false
  · constructor
    · intro h
      rfl
    · intro h
      rfl

/- ACTUAL PROOF OF Bool.coe_false_iff_false -/

example : ∀(a b : Bool), (a = false ↔ b = false) ↔ (!a) = (!b) := by
  decide