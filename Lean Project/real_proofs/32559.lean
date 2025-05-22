import Init.Core
import Init.SimpLemmas





example {α : Sort u} {c : Prop} {_ : Decidable c} (a b : α) (h : c = True) : (if c then a else b) = a := by
  simp [h]