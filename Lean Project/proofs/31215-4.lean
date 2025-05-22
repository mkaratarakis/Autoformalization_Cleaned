import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]
  rw [Nat.sub_self]

/- ACTUAL PROOF OF Nat.add_sub_self_right -/

example (a b : Nat) : (a + b) - b = a := by
  rw [Nat.add_comm]; apply add_sub_self_left