import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n : Nat) : 1 <<< n = 2 ^ n := by
  rw [shl_eq_mul_pow]
  simp

/- ACTUAL PROOF OF Nat.one_shiftLeft -/

example (n : Nat) : 1 <<< n = 2 ^ n := by
  rw [shiftLeft_eq, Nat.one_mul]