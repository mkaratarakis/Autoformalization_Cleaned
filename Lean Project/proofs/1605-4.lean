import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : range (succ n) = range n ++ [n] := by
  rw [range_eq_range']
  rw [range'_succ]
  rw [Nat.zero_add]
  rw [range_eq_range']
  rfl

/- ACTUAL PROOF OF List.range_succ -/

example (n : Nat) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_1_concat, Nat.zero_add]