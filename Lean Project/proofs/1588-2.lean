import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  cases n with
  | zero =>
    simp [range']
    rfl
  | succ n' =>
    simp [range']
    rw [range'_concat_single]
    rfl

/- ACTUAL PROOF OF List.range'_1_concat -/

example (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]