import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  apply Iff.intro
  · intro h
    have h1 : a ∧ b := And.left (And.left h)
    have h2 : a := And.left h1
    have h3 : b := And.right h1
    have h4 : c := And.right (And.left h)
    have h5 : d := And.right h
    exact And.intro (And.intro (And.intro h2 h4) h3) h5
  · intro h
    have h1 : a ∧ c := And.left (And.left h)
    have h2 : a := And.left h1
    have h3 : c := And.right h1
    have h4 : b := And.right (And.left h)
    have h5 : d := And.right h
    exact And.intro (And.intro (And.intro h2 h4) h3) h5

/- ACTUAL PROOF OF and_and_and_comm -/

example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]