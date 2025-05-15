import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [add_comm]
  apply Nat.div_mod_uniq
  · rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by assumption))]
    rw [Nat.mod_mod_of_dvd (by exact Nat.dvd_mul_right a b)]
    rw [Nat.mod_eq_of_lt (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (by assumption)) (by assumption))]
  · rw [Nat.mod_mod_of_dvd (by exact Nat.dvd_mul_right a b)]
    rw [Nat.mod_eq_of_lt (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (by assumption)) (by assumption))]
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by assumption))]
  · rw [Nat.mod_mod_of_dvd (by exact Nat.dvd_mul_right a b)]
    rw [Nat.mod_eq_of_lt (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (by assumption)) (by assumption))]
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by assumption))]
  · rw [Nat.mod_mod_of_dvd (by exact Nat.dvd_mul_right a b)]
    rw [Nat.mod_eq_of_lt (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero (by assumption)) (by assumption))]
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by assumption))]

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]