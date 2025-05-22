import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (n : Nat) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_1_concat, Nat.zero_add]