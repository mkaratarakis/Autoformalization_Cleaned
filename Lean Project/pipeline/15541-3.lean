import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Add.comm]
  apply div_mod_uniq
  · rw [mul_div_cancel_left _ (pos_of_ne_zero (by assumption))]
    rw [mod_mod_of_dvd (by exact dvd_mul_right a b)]
    rw [mod_eq_of_lt (mul_lt_mul_left (pos_of_ne_zero (by assumption)) (by assumption))]
  · rw [mod_mod_of_dvd (by exact dvd_mul_right a b)]
    rw [mod_eq_of_lt (mul_lt_mul_left (pos_of_ne_zero (by assumption)) (by assumption))]
    rw [mul_div_cancel_left _ (pos_of_ne_zero (by assumption))]
  · rw [mod_mod_of_dvd (by exact dvd_mul_right a b)]
    rw [mod_eq_of_lt (mul_lt_mul_left (pos_of_ne_zero (by assumption)) (by assumption))]
    rw [mul_div_cancel_left _ (pos_of_ne_zero (by assumption))]
  · rw [mod_mod_of_dvd (by exact dvd_mul_right a b)]
    rw [mod_eq_of_lt (mul_lt_mul_left (pos_of_ne_zero (by assumption)) (by assumption))]
    rw [mul_div_cancel_left _ (pos_of_ne_zero (by assumption))]

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]