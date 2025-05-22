import Init.Classical
import Init.ByCases





example [Decidable P] :
    (if P then some x else none) = some y ↔ P ∧ x = y := by
  split <;> simp_all