import Init.Data.List.Pairwise
import Init.Data.List.Erase

open List
open Nodup
open Nat
variable [BEq α]

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  have : a ∈ filter (· ≠ b) l ↔ a ≠ b ∧ a ∈ l := by
    apply mem_filter
  rw [this]
  have : ∀ {x y : α}, x ≠ y ↔ ¬x = y := by
    intros
    apply not_iff_not_of_iff
    apply eq_comm
  rw [this]
  rfl

/- ACTUAL PROOF OF List.Nodup.mem_erase_iff -/

example [LawfulBEq α] {a : α} (d : Nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [Nodup.erase_eq_filter d, mem_filter, and_comm, bne_iff_ne]