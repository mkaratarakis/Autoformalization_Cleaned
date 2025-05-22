import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [mod_def, mod_def, mod_def]
  simp [mul_comm, Nat.mul_div_cancel_left]
  rw [add_comm]
  rw [← Nat.add_mul_div_left]
  rw [Nat.mul_div_assoc]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]
  rw [Nat.div_eq_of_lt]


/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]