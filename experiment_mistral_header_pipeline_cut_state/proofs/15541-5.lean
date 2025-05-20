import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  have h1 : x = a * (x / a) + x % a := Nat.div_add_mod x a
  rw [h1]
  rw [Nat.mul_add]
  rw [Nat.add_comm (a * (x / a)) (x % a)]
  rw [← Nat.mod_add_div (x / a) b]
  rw [Nat.mul_mod_right]
  rw [Nat.mul_mod_right]
  rfl

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]