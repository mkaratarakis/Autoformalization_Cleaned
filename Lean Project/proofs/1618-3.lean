import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {i : Nat} {x : α} {l : List α} : (i, x) ∈ l.zipIdx ↔ l.get? i = some x := by
  constructor
  · intro h
    rw [mem_zipIdx] at h
    rcases h with ⟨h_lt, h_eq⟩
    rw [get?_eq_some]
    exact ⟨h_lt, h_eq⟩
  · intro h
    rw [get?_eq_some] at h
    rcases h with ⟨h_lt, h_eq⟩
    rw [mem_zipIdx]
    exact ⟨h_lt, h_eq⟩

/- ACTUAL PROOF OF List.mk_mem_enum_iff_getElem? -/

example {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]