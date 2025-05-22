import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  apply Iff.intro
  · intro h
    exact And.intro (And.intro h.left.left h.left.right) (And.intro h.left.left h.right)
  · intro h
    exact And.intro h.left.left (And.intro h.left.right h.right.right)

/- ACTUAL PROOF OF and_and_left -/

example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]