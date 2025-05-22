import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    cases h₁
    · left
      exact And.intro h₁ h₂
    · right
      exact And.intro h₁ h₂
  · rintro (h | h)
    · exact And.intro (Or.inl h.left) h.right
    · exact And.intro (Or.inr h.left) h.right

/- ACTUAL PROOF OF or_and_right -/

example : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  rw [@and_comm (a ∨ b), and_or_left, @and_comm c, @and_comm c]