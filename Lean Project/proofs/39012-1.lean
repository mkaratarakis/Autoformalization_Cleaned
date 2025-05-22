import Init.Classical
import Init.ByCases




example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  by_cases h : P
  · -- Case 1: P is true
    have : (if P then some x else none) = some x := by simp [h]
    calc
      (if P then some x else none) = some x := this
      _ = some y := by simp [h, x = y]
      _ ↔ P ∧ x = y := by simp [h]

  · -- Case 2: P is false
    have : (if P then some x else none) = none := by simp [h]
    have : some y ≠ none := by simp
    calc
      (if P then some x else none) ≠ some y := by simp [this]
      _ ↔ P ∧ x = y := by simp [h]

/- ACTUAL PROOF OF ite_some_none_eq_some -/

example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all