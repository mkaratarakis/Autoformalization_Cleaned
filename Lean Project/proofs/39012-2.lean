import Init.Classical
import Init.ByCases




example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  by_cases h : P
  · -- Case 1: P is true
    have : (if P then some x else none) = some x := by simp [h]
    rw [this]
    constructor
    · intro hxy
      apply And.intro
      · exact h
      · exact hxy
    · intro hconj
      apply hconj.right
  · -- Case 2: P is false
    have : (if P then some x else none) = none := by simp [h]
    rw [this]
    constructor
    · intro hxy
      apply False.elim
      apply h
      apply hxy
    · intro hconj
      apply False.elim
      exact h hconj.left

/- ACTUAL PROOF OF ite_some_none_eq_some -/

example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all