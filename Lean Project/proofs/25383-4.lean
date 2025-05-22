import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b:Bool), (b = false → b = true) ↔ (b = true) := by
intro b
apply Iff.intro
  . intros h
    exact h rfl
  . intros h _
    rfl

/- ACTUAL PROOF OF Bool.eq_false_imp_eq_true -/

example : ∀(b:Bool), (b = false → b = true) ↔ (b = true) := by
  decide