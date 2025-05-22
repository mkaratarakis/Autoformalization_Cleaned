import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h
  · -- Case 1: p is false
    apply propext
    constructor
    · intro h1
      have : p := by simp [h1]
      contradiction
    · intro h1
      have : p := by simp [h1]
      contradiction
  · -- Case 2: p is true
    apply propext
    constructor
    · intro h1
      have : q := by simp [h1]
      exact ⟨h, this⟩
    · intro h1
      have : q := by simp [h1]
      exact this

/- ACTUAL PROOF OF ite_false_same -/

example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h <;> (rename_i g; simp [g])