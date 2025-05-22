import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right, lt_succ_self]