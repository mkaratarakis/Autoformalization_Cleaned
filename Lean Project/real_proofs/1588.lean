import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]