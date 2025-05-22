import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : m ∈ range n ↔ m < n := by
  unfold range
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp
    by_cases h : m = n
    · subst h
      simp
    · rw [ih]
      simp [*]
      exact ⟨fun h => by simp [*], fun h => by simp [*]⟩

/- ACTUAL PROOF OF List.mem_range -/

example {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]