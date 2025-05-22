import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {x : Nat × α} {l : List α} (h : x ∈ zipIdx l) : x.1 < length l := by
  simp only [zipIdx, mem_map, Prod.exists, bex_def, mem_bind, mem_range] at h
  exact h

/- ACTUAL PROOF OF List.fst_lt_of_mem_enum -/

example {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h