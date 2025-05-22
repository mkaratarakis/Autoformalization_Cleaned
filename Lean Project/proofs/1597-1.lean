import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  rw [range, range]
  rw [range'_eq]
  rw [range'_eq]
  rw [range'_sublist]

/- ACTUAL PROOF OF List.range_sublist -/

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]