import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example (n : Nat) : length (iota n) = n := by
  simp [iota_eq_reverse_range']