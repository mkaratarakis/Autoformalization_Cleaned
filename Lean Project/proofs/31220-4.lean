import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.sub_add_cancel h]
  rfl

/- ACTUAL PROOF OF Nat.sub_add_cancel -/

example {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm, Nat.add_sub_of_le h]