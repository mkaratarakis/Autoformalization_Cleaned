import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat



example (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm, lcm, Nat.mul_comm n m, gcd_comm n m]