import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : Pairwise (· < ·) (range n) := by
  rw [range_eq_range']
  exact range'.pairwise_lt 0 n

/- ACTUAL PROOF OF List.pairwise_lt_range -/

example (n : Nat) : Pairwise (· < ·) (range n) := by
  simp (config := {decide := true}) only [range_eq_range', pairwise_lt_range']