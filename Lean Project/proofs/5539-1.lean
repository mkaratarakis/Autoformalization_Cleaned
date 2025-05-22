import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p q False ↔ p ∧ q := by
  cases h
  · -- Case 1: p is false
    simp [ite]
    exact Iff.rfl
  · -- Case 2: p is true
    simp [ite]
    exact Iff.rfl

/- ACTUAL PROOF OF if_false_right -/

example [h : Decidable p] :
    ite p q False ↔ p ∧ q := by
  cases h <;> (rename_i g; simp [g])