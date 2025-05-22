import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [add_comm]
  rw [add_sub_cancel_left]
  rfl

/- ACTUAL PROOF OF Nat.sub_add_cancel -/

example {n m : Nat} (h : m ≤ n) : n - m + m = n := by
  rw [Nat.add_comm, Nat.add_sub_of_le h]