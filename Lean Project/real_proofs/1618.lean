import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]