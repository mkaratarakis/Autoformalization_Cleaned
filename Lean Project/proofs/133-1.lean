import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nodup
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [erase_eq_filter (not_mem_erase_of_nodup d)]
  rw [mem_filter]
  rw [and_comm]
  rw [ne_eq_true]
  rfl

/- ACTUAL PROOF OF List.Nodup.mem_erase_iff -/

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [Nodup.erase_eq_filter d, mem_filter, and_comm, bne_iff_ne]