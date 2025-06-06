import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n : Nat} : n ∉ range n := by
  unfold range
  induction n with
  | zero =>
    simp [range.loop]
  | succ n ih =>
    simp [range.loop]
    intro h
    exact Nat.not_succ_le_self n (mem_iff_lt.1 h)

/- ACTUAL PROOF OF List.not_mem_range_self -/

example {n : Nat} : n ∉ range n := by
  simp