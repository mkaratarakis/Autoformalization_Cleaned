import Init.Data.List.Sublist
import Init.Data.List.Count

open List
open Nat
variable (p q : α → Bool)
variable {p q}
variable [BEq α]
variable [LawfulBEq α]

example (a b : α) (n : Nat) : count a (replicate n b) = if b == a then n else 0 := by
  by_cases h : b == a
  · rw [h]
    exact count_replicate_self a n
  · rw [count_eq_zero]
    intro h'
    rw [mem_replicate] at h'
    exact h h'

/- ACTUAL PROOF OF List.count_replicate -/

example (a b : α) (n : Nat) : count a (replicate n b) = if b == a then n else 0 := by
  split <;> (rename_i h; simp only [beq_iff_eq] at h)
  · exact ‹b = a› ▸ count_replicate_self ..
  · exact count_eq_zero.2 <| mt eq_of_mem_replicate (Ne.symm h)