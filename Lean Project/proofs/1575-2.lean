import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (s n step) : range' s (n + 1) step = s :: range' (s + step) n step := by
  rw [Nat.succ_eq_add_one, range']

/- ACTUAL PROOF OF List.range'_succ -/

example (s n step) : range' s (n + 1) step = s :: range' (s + step) n step := by
  simp [range', Nat.add_succ, Nat.mul_succ]