import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  apply Iff.intro
  · intro h
    exact And.intro (And.intro (And.intro h.left.left.left h.left.right) h.left.left.right) h.right
  · intro h
    exact And.intro (And.intro (And.intro h.left.left.left h.left.right) h.left.left.right) h.right

/- ACTUAL PROOF OF and_and_and_comm -/

example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]