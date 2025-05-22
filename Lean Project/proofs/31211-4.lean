import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  exact Nat.add_le_add_left h k

/- ACTUAL PROOF OF Nat.add_le_add_right -/

example {n m : Nat} (h : n ≤ m) (k : Nat) : n + k ≤ m + k := by
  rw [Nat.add_comm n k, Nat.add_comm m k]
  apply Nat.add_le_add_left
  assumption