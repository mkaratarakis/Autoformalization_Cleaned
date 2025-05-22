import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {i : Nat} {x : α} {l : List α} : (i, x) ∈ l.zipIdx ↔ l[i]? = some x := by
  constructor
  · intro h
    rcases h with ⟨j, y, h_eq⟩
    rw [← h_eq]
    exact get?_eq_some_iff.2 ⟨j < length l, rfl⟩
  · intro h
    rw [get?_eq_some_iff] at h
    rcases h with ⟨h_lt, h_eq⟩
    exact mem_zipIdx.2 ⟨h_lt, h_eq⟩

/- ACTUAL PROOF OF List.mk_mem_enum_iff_getElem? -/

example {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]