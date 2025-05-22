import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  cases hc : Decidable.casesOn (by simp [h]) c with
  | isTrue hc => rfl
  | isFalse hc => exact absurd hc h

/- ACTUAL PROOF OF dite_cond_eq_true -/

example {α : Sort u} {c : Prop} {_ : Decidable c} {t : c → α} {e : ¬ c → α} (h : c = True) : (dite c t e) = t (of_eq_true h) := by
  simp [h]