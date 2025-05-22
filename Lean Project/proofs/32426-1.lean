import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  rw [add_comm (a := a) (b := b), add_comm (a := a) (b := c)]
  rw [max_add_right]

/- ACTUAL PROOF OF Nat.add_max_add_left -/

example (a b c : Nat) : max (a + b) (a + c) = a + max b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_max_add_right ..