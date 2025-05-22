import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  rw [range, range]
  apply Iff.intro
  · intro h
    cases m
    · simp
    · simp [Nat.succ_le_succ_iff] at h
      exact h
  · intro h
    exact sublist_of_le h

/- ACTUAL PROOF OF List.range_sublist -/

example {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]