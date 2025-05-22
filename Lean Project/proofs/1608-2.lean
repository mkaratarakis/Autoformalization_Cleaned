import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example {m n : Nat} : m ∈ (range' 1 n).reverse ↔ 1 ≤ m ∧ m ≤ n := by
  rw [mem_reverse]
  simp
  rw [mem_range']
  simp
  split
  · intro h
    exact And.intro (Nat.le_of_lt_succ h.1) h.2
  · intro h
    exact And.intro (Nat.lt_of_le_of_lt h.1 h.2) h.2

/- ACTUAL PROOF OF List.mem_iota -/

example {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]