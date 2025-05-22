import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  rw [min_add_add_left]

/- ACTUAL PROOF OF Nat.add_min_add_left -/

example (a b c : Nat) : min (a + b) (a + c) = a + min b c := by
  repeat rw [Nat.add_comm a]
  exact Nat.add_min_add_right ..