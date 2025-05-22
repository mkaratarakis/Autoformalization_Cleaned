import Init.Classical
import Init.ByCases





example [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  by_cases h : P <;> simp [h]