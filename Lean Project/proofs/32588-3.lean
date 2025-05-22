import Init.Core
import Init.SimpLemmas




example : (a ∨ b ↔ b) ↔ (a → b) := by
  have h1 : (a ∨ b ↔ b) → (a → b) := by
    intro h
    intro a
    apply (Propext.mp h).mp
    apply Or.inl
    exact a
  have h2 : (a → b) → (a ∨ b ↔ b) := by
    intro h
    apply Iff.intro
    · intro hb
      cases hb with
      | inl ha => exact h ha
      | inr hb => exact hb
    · intro b
      apply Or.inr
      exact b
  exact ⟨h1, h2⟩

/- ACTUAL PROOF OF or_iff_right_iff_imp -/

example : (a ∨ b ↔ b) ↔ (a → b) := by
  rw [or_comm, or_iff_left_iff_imp]