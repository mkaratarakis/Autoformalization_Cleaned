import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example : range' s n step = [] ↔ n = 0 := by
  constructor
  · intro h
    simp only [range'_eq_nil] at h
    exact h
  · intro h
    rw [h]
    simp only [range'_eq_nil]

/- ACTUAL PROOF OF List.range'_eq_nil -/

example : range' s n step = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range']