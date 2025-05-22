import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)


example : 0 < countP p l ↔ ∃ a ∈ l, p a := by
  simp only [countP_eq_length_filter, length_pos_iff_exists_mem, mem_filter, exists_prop]