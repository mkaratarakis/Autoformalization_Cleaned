import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example {x m n : Nat} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  rw [Nat.div_eq_iff_eq_mul_left (Nat.pow_pos hx) (Nat.pow_dvd_pow _ h), Nat.pow_sub_mul_pow _ h]