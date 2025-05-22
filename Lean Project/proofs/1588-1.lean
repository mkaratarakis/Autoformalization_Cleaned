import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  cases n with
  | zero =>
    simp [range', add_zero]
  | succ n' =>
    simp [range', Nat.succ_add]
    rw [range'_concat_single]
    rfl

/- ACTUAL PROOF OF List.range'_1_concat -/

example (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]