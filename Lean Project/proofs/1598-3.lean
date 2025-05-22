import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  rw [range_eq_range']
  rw [range_eq_range']
  constructor
  · intro h
    by_cases hm0 : m = 0
    · exact le_of_eq hm0
    · have : m - 1 < n := by
        apply Nat.lt_of_le_of_lt (Nat.sub_le _ _)
        exact Nat.lt_succ_self _
      cases' n with n
      · simp at h
      · simp only [range', List.subsetDef] at h
        have : ∀ i, i ∈ range' 0 m → i < n := by
          intro i hi
          obtain ⟨j, rfl⟩ := hi
          exact (h j (List.mem_range.mpr ⟨j, (Nat.lt_succ_iff.mpr (Nat.lt_of_succ_lt_succ j))⟩)).left
        have := this m (by simp)
        exact Nat.le_of_lt_succ this
  · intro h
    apply List.subset_of_forall_of_length_le
    · intro a ha
      simp at ha
      obtain ⟨i, rfl⟩ := ha
      exact ⟨i, by simpa using h⟩
    · simp [range', range.length, h]

/- ACTUAL PROOF OF List.range_subset -/

example {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right, lt_succ_self]