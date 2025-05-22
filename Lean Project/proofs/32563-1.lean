import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {_ : Decidable c} (a b : α) (h : c = False) : (if c then a else b) = b := by
  rw [h]
  rfl

/- ACTUAL PROOF OF ite_cond_eq_false -/

example {α : Sort u} {c : Prop} {_ : Decidable c} (a b : α) (h : c = False) : (if c then a else b) = b := by
  simp [h]