import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]
  rw [Nat.add_sub_cancel_left]

/- ACTUAL PROOF OF Nat.add_sub_self_right -/

example (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]; apply add_sub_self_left