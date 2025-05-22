import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  rw [dite_eq_ite]
  rw [ite_eq_true_eq_left]
  rw [h]

/- ACTUAL PROOF OF dite_cond_eq_true -/

example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  simp [h]