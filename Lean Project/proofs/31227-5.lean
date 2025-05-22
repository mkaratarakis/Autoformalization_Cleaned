import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m]
  apply Nat.sub_sub_cancel_left

/- ACTUAL PROOF OF Nat.add_sub_add_left -/

example (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]