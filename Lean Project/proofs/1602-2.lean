import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range]
  simp [range', take]
  rw [take_eq_nil.symm]
  apply Nat.lt_irrefl

/- ACTUAL PROOF OF List.getElem_range -/

example {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range_eq_range']