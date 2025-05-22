import Init.Core
import Init.SimpLemmas




example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d
  · refl
  · refl

/- ACTUAL PROOF OF ite_self -/

example {α : Sort u} {c : Prop} {d : Decidable c} (a : α) : ite c a a = a := by
  cases d <;> rfl