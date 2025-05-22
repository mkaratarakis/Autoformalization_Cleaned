import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [add_comm k n, add_comm k m]
  rw [Nat.sub_eq_of_eq_add (n + k) (m + k)]
  rfl

/- ACTUAL PROOF OF Nat.add_sub_add_left -/

example (k n m : Nat) : (k + n) - (k + m) = n - m := by
  rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]