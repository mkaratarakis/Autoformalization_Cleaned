import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]


example (l : List α) (a : α) : l.filter (· == a) = replicate (count a l) a := by
  simp only [count, countP_eq_length_filter, eq_replicate, mem_filter, beq_iff_eq]
  exact ⟨trivial, fun _ h => h.2⟩