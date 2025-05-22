import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d
  · rfl
  · rfl

/- ACTUAL PROOF OF ite_self -/

example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d <;> rfl