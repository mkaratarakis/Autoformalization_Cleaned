import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x z : Nat) : (x + z) % x = z % x := by
  rw [add_comm]
  rw [add_mod]

/- ACTUAL PROOF OF Nat.add_mod_left -/

example (x z : Nat) : (x + z) % x = z % x := by
  rw [Nat.add_comm, add_mod_right]