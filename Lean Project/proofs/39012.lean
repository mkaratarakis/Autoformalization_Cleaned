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
      · exact Option.some.inj hxy
    · intro hconj
      rw [hconj.right]
  · -- Case 2: P is false
    have : (if P then some x else none) = none := by simp [h]
    rw [this]
    constructor
    · intro hxy
      exact (False.elim (Option.noConfusion hxy))
    · intro hconj
      exact absurd hconj.left h

/- ACTUAL PROOF OF ite_some_none_eq_some -/

example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all