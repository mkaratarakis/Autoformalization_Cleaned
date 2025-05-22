import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h
  · -- Case 1: p is false
    have : ¬p := h
    have : ¬(p ∧ q) := by
      intro hpq
      apply this
      exact hpq.left
    apply propext
    exact Iff.intro
      (fun h1 : (if p then q else p) => by
        cases h1
        contradiction)
      (fun h1 : p ∧ q => by
        exfalso
        apply this
        exact h1.left)
  · -- Case 2: p is true
    have : p := h
    apply propext
    exact Iff.intro
      (fun h1 : (if p then q else p) => by
        cases h1
        exact h1)
      (fun h1 : p ∧ q => by
        exact h1.right)

/- ACTUAL PROOF OF ite_false_same -/

example (p q : Prop) [h : Decidable p] : (if p then q else p) = (p ∧ q) := by
  cases h <;> (rename_i g; simp [g])