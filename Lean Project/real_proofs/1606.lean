import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (n : Nat) : Nodup (range n) := by
  simp (config := {decide := true}) only [range_eq_range', nodup_range']