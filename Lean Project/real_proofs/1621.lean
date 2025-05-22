import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h