import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (l : List α) (n : Nat) : (enum l)[n]? = l[n]?.map fun a => (n, a) := by
  rw [enum]
  rw [enumFrom_eq_mapIndex]
  rw [zero_add]
  rfl

/- ACTUAL PROOF OF List.getElem?_enum -/

example (l : List α) (n : Nat) : (enum l)[n]? = l[n]?.map fun a => (n, a) := by
  rw [enum, getElem?_enumFrom, Nat.zero_add]