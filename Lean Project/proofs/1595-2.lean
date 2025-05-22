import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n : Nat} : n ∉ range n := by
  unfold range
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    simp [range.loop]
    apply ih

/- ACTUAL PROOF OF List.not_mem_range_self -/

example {n : Nat} : n ∉ range n := by
  simp