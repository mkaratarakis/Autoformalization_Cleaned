import Init.Core
import Init.SimpLemmas




example {x y u v : α} {s : Decidable b} [Decidable c]
    (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases s <;> simp [h₁]
  · exact h₂ trivial
  · exact h₃ not_iff_not_of_iff.mp h₁

/- ACTUAL PROOF OF ite_congr -/

example {x y u v : α} {s : Decidable b} [Decidable c]
    (h₁ : b = c) (h₂ : c → x = u) (h₃ : ¬ c → y = v) : ite b x y = ite c u v := by
  cases Decidable.em c with
  | inl h => rw [if_pos h]; subst b; rw [if_pos h]; exact h₂ h
  | inr h => rw [if_neg h]; subst b; rw [if_neg h]; exact h₃ h