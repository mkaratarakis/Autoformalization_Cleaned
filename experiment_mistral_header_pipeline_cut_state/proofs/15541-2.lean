import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [add_comm]
  rw [← Nat.div_add_mod (x % (a * b)), ← Nat.mod_add_div]
  rw [Nat.mul_mod_right]
  rw [Nat.div_mod_div_cancel]
  rw [Nat.mul_mod_right]
  rfl

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]