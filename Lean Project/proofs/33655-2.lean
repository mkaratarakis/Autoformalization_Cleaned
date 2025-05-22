import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ zipIdx n l ↔ n ≤ i ∧ l[i - n]? = x := by
  constructor
  · intro h
    obtain ⟨k, h1, h2⟩ := h
    simp at h1
    obtain ⟨rfl, h3⟩ := h1
    simp at h3
    exact ⟨le_add_left _ _, h3⟩
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨k, rfl⟩ := exists_eq_add_of_le h1
    simp at h2
    exact mem_zipIdx.mpr ⟨k, rfl, h2⟩

/- ACTUAL PROOF OF List.mk_mem_enumFrom_iff_le_and_getElem?_sub -/

example {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l[i - n]? = x := by
  if h : n ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_enumFrom_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ k, n + k ≠ i := by rintro k rfl; simp at h
    simp [h, mem_iff_get?, this]