import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [mod_def, mod_def, mod_def]
  rw [Nat.add_mul_div_left]
  rw [Nat.mul_div_assoc]
  rw [Nat.mul_div_left]
  exact Nat.div_eq_of_lt (Nat.lt_of_mul_lt_mul_left (Nat.zero_lt_succ b) (Nat.zero_lt_succ a))

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]