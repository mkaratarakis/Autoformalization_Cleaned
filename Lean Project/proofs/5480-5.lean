import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  apply Iff.intro
  · intro h
    cases h
    case intro h1 h2 =>
      cases h1
      case intro h1_1 h1_2 =>
        cases h1_1
        case intro h1_1_1 h1_1_2 =>
          exact And.intro (And.intro (And.intro h1_1_1 h1_2) h1_1_2) h2
  · intro h
    cases h
    case intro h1 h2 =>
      cases h1
      case intro h1_1 h1_2 =>
        cases h1_1
        case intro h1_1_1 h1_1_2 =>
          exact And.intro (And.intro (And.intro h1_1_1 h1_1_2) h1_2) h2

/- ACTUAL PROOF OF and_and_and_comm -/

example : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d := by
  rw [← and_assoc, @and_right_comm a, and_assoc]