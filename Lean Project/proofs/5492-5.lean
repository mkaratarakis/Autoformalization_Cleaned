import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  apply Iff.intro
  · intro h
    cases h
    · apply And.intro
      · left
        apply And.left
        assumption
      · left
        apply And.right
        assumption
    · apply And.intro
      · right
        assumption
      · right
        assumption
  · intro h
    cases h.left
    · left
      constructor
      · exact h.left
      · apply Or.elim h.right
        · intro h1
          exact h1
        · intro h1
          exact h1
    · right
      apply Or.elim h.left
      · intro h1
        exact h1
      · intro h1
        exact h1

/- ACTUAL PROOF OF and_or_right -/

example : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) := by
  rw [@or_comm (a ∧ b), or_and_left, @or_comm c, @or_comm c]