import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by

  have i := x.1
  have a := x.2
  have h1 := List.length_enumFrom n l
  simp at h1
  have h2 : i < n + length l
  exact Nat.lt_add_of_le_right h1 (Nat.zero_le i)
  exact h2

/- ACTUAL PROOF OF List.fst_lt_add_of_mem_enumFrom -/

example {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt