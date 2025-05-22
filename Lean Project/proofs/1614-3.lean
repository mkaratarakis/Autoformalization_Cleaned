import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ zipIdx n l) :
    x.1 < n + length l := by

  have : x ∈ zipIdx n l
  simp at h

  have : x.1 < n + length l
  apply Nat.lt_add_of_le_right
  apply Nat.zero_le

  exact h

/- ACTUAL PROOF OF List.fst_lt_add_of_mem_enumFrom -/

example {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt