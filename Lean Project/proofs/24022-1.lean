import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm]
  rw [lcm]
  rw [mul_comm]
  exact gcd_comm m n

/- ACTUAL PROOF OF Nat.lcm_comm -/

example (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm, lcm, Nat.mul_comm n m, gcd_comm n m]