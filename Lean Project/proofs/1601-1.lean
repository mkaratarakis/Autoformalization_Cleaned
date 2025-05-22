import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {s m n : Nat} (step0 : 0 < step) :
    range' s m step ⊆ range' s n step ↔ m ≤ n := by
  constructor
  · intro h
    by_contra hn
    have := lt_of_lt_of_le hn (List.length_range' _ _ _)
    have hsub := List.Sublist.subset h
    have hmem := List.mem_range'.2 ⟨n, by rfl⟩
    have hnmem : n ∉ range' s m step := by
      intro hmem'
      apply Nat.noConfusion (List.mem_range'.1 hmem').1
      exact (Nat.lt_irrefl _ this).elim
    exact hnmem (hsub hmem)
  · intro hmn
    apply List.Sublist.subset
    intro x hx
    rcases List.mem_range'.1 hx with ⟨i, hi, rfl⟩
    exact List.mem_range'.2 ⟨i, (Nat.lt_trans hi hmn)⟩

/- ACTUAL PROOF OF List.range'_subset_right -/

example {s m n : Nat} (step0 : 0 < step) :
    range' s m step ⊆ range' s n step ↔ m ≤ n := by
  refine ⟨fun h => Nat.le_of_not_lt fun hn => ?_, fun h => (range'_sublist_right.2 h).subset⟩
  have ⟨i, h', e⟩ := mem_range'.1 <| h <| mem_range'.2 ⟨_, hn, rfl⟩
  exact Nat.ne_of_gt h' (Nat.eq_of_mul_eq_mul_left step0 (Nat.add_left_cancel e))