import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ zipIdx (range n) l ↔ n ≤ i ∧ l[i - n]? = some x := by
  constructor
  · intro h
    obtain ⟨⟨j, _⟩, x', h1, rfl⟩ := h
    simp only [Nat.sub_add_cancel] at h1
    exact ⟨h1, by simp [h1]⟩
  · intro h
    obtain ⟨hle, hx⟩ := h
    use i - n
    simp only [Nat.sub_add_cancel hle]
    exact ⟨hle, hx, rfl⟩

/- ACTUAL PROOF OF List.mk_mem_enumFrom_iff_le_and_getElem?_sub -/

example {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l[i - n]? = x := by
  if h : n ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_enumFrom_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ k, n + k ≠ i := by rintro k rfl; simp at h
    simp [h, mem_iff_get?, this]