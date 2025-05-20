import Init.Classical
import Init.ByCases




example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  byCases h: c
  case posit =>
    have h : (if c then t else t) = t := if_true t t
    exact h
  case negat =>
    have h : (if c then t else t) = t := if_false t t
    exact h
  done

/- ACTUAL PROOF OF ite_id -/

example [Decidable c] {α} (t : α) : (if c then t else t) = t := by
  split <;> rfl