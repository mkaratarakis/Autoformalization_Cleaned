import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat



example (m : Nat) : lcm m 0 = 0 := by
  simp [lcm]