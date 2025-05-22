import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (x n : Nat) : x <<< n >>> n = x := by
  rw [shiftr_shiftl]

/- ACTUAL PROOF OF Nat.shiftLeft_shiftRight -/

example (x n : Nat) : x <<< n >>> n = x := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]