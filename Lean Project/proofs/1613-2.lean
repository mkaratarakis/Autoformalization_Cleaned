import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (m n : Nat) : take m (range n) = range (min m n) := by
  apply List.take_eq_of_length
  simp [List.length_range, min_def]

/- ACTUAL PROOF OF List.take_range -/

example (m n : Nat) : take m (range n) = range (min m n) := by
  apply List.ext_getElem
  · simp
  · simp (config := { contextual := true }) [← getElem_take, Nat.lt_min]