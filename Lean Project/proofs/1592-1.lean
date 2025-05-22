import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    simp [mem_range'] at hi
    rcases hi with ⟨rfl, hlt⟩
    constructor
    · apply Nat.le_add_left
    · exact Nat.lt_add_right _ _ hlt
  · intro h
    rcases h with ⟨hle, hlt⟩
    use m - s
    constructor
    · rw [Nat.sub_add_cancel hle]
    · exact Nat.sub_lt hlt (Nat.le_add_left _ _)

/- ACTUAL PROOF OF List.mem_range'_1 -/

example : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩