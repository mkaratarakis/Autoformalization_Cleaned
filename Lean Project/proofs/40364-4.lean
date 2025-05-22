import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Notation
import Init.Data.List.Basic

open List
open Decidable List
variable {α : Type u} {β : Type v} {γ : Type w}

example {a : α} {as : List α} (bs : List α) : a ∈ as → a ∈ as ++ bs := by
  intro h
  induction as generalizing bs
  · contradiction
  · cases h
    · apply List.Mem.head
    · apply List.Mem.tail
      exact as_ih bs a_a

/- ACTUAL PROOF OF List.mem_append_of_mem_left -/

example {a : α} {as : List α} (bs : List α) : a ∈ as → a ∈ as ++ bs := by
  intro h
  induction h with
  | head => apply Mem.head
  | tail => apply Mem.tail; assumption