import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]


example (a b : α) (n : Nat) : count a (replicate n b) = if b == a then n else 0 := by
  split <;> (rename_i h; simp only [beq_iff_eq] at h)
  · exact ‹b = a› ▸ count_replicate_self ..
  · exact count_eq_zero.2 <| mt eq_of_mem_replicate (Ne.symm h)