import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : m ∈ range n ↔ m < n := by
  unfold range
  induction n with
  | zero =>
    simp [range]
  | succ n ih =>
    simp [range]
    by_cases h : m = n
    · subst h
      simp
    · by_cases h' : m < n
      · simp [h', ih h']
      · simp [h']
        intro h''
        apply Nat.not_lt_of_ge
        exact h''

/- ACTUAL PROOF OF List.mem_range -/

example {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]