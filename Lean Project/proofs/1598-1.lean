import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  rw [range_eq_range']
  rw [range_eq_range']
  rw [range'_subset_range']
  rw [le_iff_lt_succ]
  rfl

/- ACTUAL PROOF OF List.range_subset -/

example {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right, lt_succ_self]