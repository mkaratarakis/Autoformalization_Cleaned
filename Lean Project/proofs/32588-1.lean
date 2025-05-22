import Init.Core
import Init.SimpLemmas




example : (a ∨ b ↔ b) ↔ (a → b) := by
  have h1 : (a ∨ b ↔ b) → (a → b) := by
    intro h
    intro a
    apply (iff.mp h).mp
    left
    exact a
  have h2 : (a → b) → (a ∨ b ↔ b) := by
    intro h
    apply propext
    show a ∨ b ↔ b
    constructor
    · intro hb
      cases hb
      · exact h hb
      · exact hb
    · intro b
      right
      exact b
  exact ⟨h1, h2⟩

/- ACTUAL PROOF OF or_iff_right_iff_imp -/

example : (a ∨ b ↔ b) ↔ (a → b) := by
  rw [or_comm, or_iff_left_iff_imp]