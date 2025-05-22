import Init.Classical
import Init.ByCases




example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  by_cases c <;> simp [h]

/- ACTUAL PROOF OF ite_id -/

example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  split <;> rfl