import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h
  · -- Case 1: p is false
    apply propext
    constructor
    · intro h1
      contradiction
    · intro h1
      contradiction
  · -- Case 2: p is true
    apply propext
    constructor
    · intro h1
      exact h1
    · intro h1
      exact h1.right

/- ACTUAL PROOF OF ite_false_same -/

example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h <;> (rename_i g; simp [g])