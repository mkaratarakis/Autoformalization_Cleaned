import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm]
  have h₁ : a * ((x / a) % b) = x % (a * b) / a * a := by
    rw [Nat.mod_div_cancel (mt Nat.dvd_iff.mp (mt Nat.dvd_zero (Nat.ne_of_gt (Nat.pos_of_ne_zero (by assumption)))))]
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by assumption))]
  have h₂ : x % a = x % (a * b) % a := by
    rw [Nat.mod_mod_of_dvd (by exact Nat.dvd_mul_right a b)]
  rw [h₁, h₂]
  rfl

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]