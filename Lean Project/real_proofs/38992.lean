import Init.Classical
import Init.ByCases





example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  split <;> rfl