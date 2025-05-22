import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : n ∈ range (n + 1) := by
  unfold range
  simp
  apply List.mem_range
  simp

/- ACTUAL PROOF OF List.self_mem_range_succ -/

example (n : Nat) : n ∈ range (n + 1) := by
  simp