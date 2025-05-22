import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d
  · exact if_pos h
  · exact if_neg h

/- ACTUAL PROOF OF ite_self -/

example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d <;> rfl