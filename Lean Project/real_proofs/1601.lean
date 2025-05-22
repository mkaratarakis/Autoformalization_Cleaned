import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example {s m n : Nat} (step0 : 0 < step) :
    range' s m step ⊆ range' s n step ↔ m ≤ n := by
  refine ⟨fun h => Nat.le_of_not_lt fun hn => ?_, fun h => (range'_sublist_right.2 h).subset⟩
  have ⟨i, h', e⟩ := mem_range'.1 <| h <| mem_range'.2 ⟨_, hn, rfl⟩
  exact Nat.ne_of_gt h' (Nat.eq_of_mul_eq_mul_left step0 (Nat.add_left_cancel e))