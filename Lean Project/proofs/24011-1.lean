import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m : Nat) : lcm 1 m = m := by
  rw [lcm]
  rw [gcd_one_right]
  simp

/- ACTUAL PROOF OF Nat.lcm_one_left -/

example (m : Nat) : lcm 1 m = m := by
  simp [lcm]