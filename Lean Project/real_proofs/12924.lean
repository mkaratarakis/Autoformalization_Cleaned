import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example : countP p l = 0 ↔ ∀ a ∈ l, ¬p a := by
  simp only [countP_eq_length_filter, length_eq_zero, filter_eq_nil]