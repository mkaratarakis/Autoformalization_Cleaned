import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  rw [range, range]
  apply Iff.intro
  · intro h
    exact Nat.le_of_lt_succ (Nat.lt_of_succ_le h)
  · intro h
    exact Nat.lt_of_le_succ h

/- ACTUAL PROOF OF List.range_sublist -/

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]