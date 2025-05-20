import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  have h1 : x = a * (x / a) + x % a := Nat.div_add_mod x a
  have h2 : x / a = b * ((x / a) / b) + (x / a) % b := Nat.div_add_mod (x / a) b
  rw [h1]
  rw [h2]
  rw [Nat.mul_add]
  rw [Nat.mul_assoc]
  simp

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]