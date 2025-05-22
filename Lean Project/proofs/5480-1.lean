import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  apply Iff.intro
  · intro h
    have h1 : a ∧ b ∧ c := And.left h
    have h2 : a ∧ b := And.left h1
    have h3 : a := And.left h2
    have h4 : b := And.right h2
    have h5 : c := And.right h1
    have h6 : d := And.right h
    exact And.intro (And.intro (And.intro h3 h5) h4) h6
  · intro h
    have h1 : a ∧ c ∧ b := And.left h
    have h2 : a ∧ c := And.left h1
    have h3 : a := And.left h2
    have h4 : c := And.right h2
    have h5 : b := And.right h1
    have h6 : d := And.right h
    exact And.intro (And.intro (And.intro h3 h4) h5) h6

/- ACTUAL PROOF OF and_and_and_comm -/

example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]