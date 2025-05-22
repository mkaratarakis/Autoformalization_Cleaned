import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m : Nat) : lcm m 0 = 0 := by
  rw [lcm]
  apply gcd_zero_right

/- ACTUAL PROOF OF Nat.lcm_zero_right -/

example (m : Nat) : lcm m 0 = 0 := by
  simp [lcm]