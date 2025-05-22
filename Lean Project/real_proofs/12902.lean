import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example : countP p l ≤ l.length := by
  simp only [countP_eq_length_filter]
  apply length_filter_le