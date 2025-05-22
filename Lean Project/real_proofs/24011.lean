import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat



example (m : Nat) : lcm 1 m = m := by
  simp [lcm]