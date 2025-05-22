import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  apply max_mul_right

/- ACTUAL PROOF OF Nat.mul_max_mul_left -/

example (a b c : Nat) : max (a * b) (a * c) = a * max b c := by
  repeat rw [Nat.mul_comm a]
  exact Nat.mul_max_mul_right ..