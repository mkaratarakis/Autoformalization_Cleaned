import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  apply Iff.intro
  · intro h
    cases h with h1 h2
    cases h2 with h2b h2c
    exact And.intro (And.intro h1 h2b) (And.intro h1 h2c)
  · intro h
    cases h with h1 h2
    cases h1 with h1a h1b
    cases h2 with h2a h2c
    exact And.intro h1a (And.intro h1b h2c)

/- ACTUAL PROOF OF and_and_left -/

example : a ∧ (b ∧ c) ↔ (a ∧ b) ∧ a ∧ c := by
  rw [and_and_and_comm, and_self]