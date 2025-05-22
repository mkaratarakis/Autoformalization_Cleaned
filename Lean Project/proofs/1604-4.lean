import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    simp [range]
    rw [ih]
    simp [map]
    rfl

/- ACTUAL PROOF OF List.range_succ_eq_map -/

example (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', Nat.add_comm, ← map_add_range']
  congr; exact funext (Nat.add_comm 1)