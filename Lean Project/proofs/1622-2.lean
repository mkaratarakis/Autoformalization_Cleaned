import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (l : List α) (n : Nat) : (zipIdx l)[n]? = l[n]?.map fun a => (n, a) := by
  rw [zipIdx]
  rw [zipIdx]
  rw [Option.map]
  simp
  rfl

/- ACTUAL PROOF OF List.getElem?_enum -/

example (l : List α) (n : Nat) : (enum l)[n]? = l[n]?.map fun a => (n, a) := by
  rw [enum, getElem?_enumFrom, Nat.zero_add]