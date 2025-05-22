import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat



example (m : Nat) : lcm 0 m = 0 := by
  simp [lcm]