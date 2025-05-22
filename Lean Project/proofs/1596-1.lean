import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : m ∈ range n ↔ m < n := by
  unfold range
  rw [range_eq_range']
  rw [mem_range']
  constructor
  · intro h
    exact h.right
  · intro h
    exact ⟨zero_le _, h⟩

/- ACTUAL PROOF OF List.mem_range -/

example {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]