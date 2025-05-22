import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    apply Or.inl
    exact And.intro ha hc
  · intro h
    cases h
    · exact And.intro (Or.inl h) h_h
    · exact And.intro (Or.inr h) h_h

/- ACTUAL PROOF OF or_and_right -/

example : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) := by
  rw [@and_comm (a ∨ b), and_or_left, @and_comm c, @and_comm c]