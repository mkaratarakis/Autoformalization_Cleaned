import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nodup
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  have : a ∈ filter (fun x => x != b) l ↔ a ≠ b ∧ a ∈ l := by
    apply mem_filter
  rw [this]
  rfl

/- ACTUAL PROOF OF List.Nodup.mem_erase_iff -/

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [Nodup.erase_eq_filter d, mem_filter, and_comm, bne_iff_ne]