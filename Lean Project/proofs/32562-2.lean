import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  rw [h]
  rfl

/- ACTUAL PROOF OF dite_cond_eq_true -/

example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  simp [h]