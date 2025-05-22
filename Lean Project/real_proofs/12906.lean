import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example : countP p l = l.length ↔ ∀ a ∈ l, p a := by
  rw [countP_eq_length_filter, filter_length_eq_length]