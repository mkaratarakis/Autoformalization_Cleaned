import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : n ∈ range (n + 1) := by
  unfold range
  induction n with
  | zero =>
    simp
    apply Mem.head
  | succ n ih =>
    simp
    apply Mem.tail _ ih

/- ACTUAL PROOF OF List.self_mem_range_succ -/

example (n : Nat) : n ∈ range (n + 1) := by
  simp