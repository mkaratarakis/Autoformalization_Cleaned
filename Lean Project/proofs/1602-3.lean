import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range]
  apply range'_nth_le
  exact h

/- ACTUAL PROOF OF List.getElem_range -/

example {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range_eq_range']