import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {a : α} {l} : [a] <+ l ↔ a ∈ l := by
  constructor
  · intro h
    exact h.subset (mem_singleton a)
  · intro h
    cases' h with x hx
    exact Sublist.append_right _ _ (Sublist.sublist_of_mem hx)

/- ACTUAL PROOF OF List.singleton_sublist -/

example {a : α} {l} : [a] <+ l ↔ a ∈ l := by
  refine ⟨fun h => h.subset (mem_singleton_self _), fun h => ?_⟩
  obtain ⟨_, _, rfl⟩ := append_of_mem h
  exact ((nil_sublist _).cons₂ _).trans (sublist_append_right ..)