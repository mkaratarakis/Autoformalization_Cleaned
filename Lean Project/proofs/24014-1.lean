import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m : Nat) : lcm m 1 = m := by
  unfold lcm
  simp [gcd_rec]

/- ACTUAL PROOF OF Nat.lcm_one_right -/

example (m : Nat) : lcm m 1 = m := by
  simp [lcm]