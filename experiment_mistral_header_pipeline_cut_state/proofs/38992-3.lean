import Init.Classical
import Init.ByCases




example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  byCases h: c
  · exact if_pos h
  · exact if_neg h
  done

/- ACTUAL PROOF OF ite_id -/

example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  split <;> rfl