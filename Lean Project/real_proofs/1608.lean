import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat


example {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]