import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  apply Iff.intro
  · intro h
    apply And.intro
    · exact And.right (And.left h)
    · apply And.intro
      · exact And.right h
      · exact And.left h
  · intro h
    apply And.intro
    · exact And.right (And.right h)
    · apply And.intro
      · exact And.left h
      · exact And.left (And.right h)

/- ACTUAL PROOF OF and_rotate -/

example : a ∧ b ∧ c ↔ b ∧ c ∧ a := by
  rw [and_left_comm, @and_comm a c]