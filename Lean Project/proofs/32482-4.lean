import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {x m n : Nat} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  have : x ^ n * x ^ (m - n) = x ^ m := by
    rw [← pow_add_monoid]
    rw [tsub_add_cancel_of_le h]
  have h_pos : x ^ n > 0 := by
    apply pow_pos_of_pos
    exact hx
  rw [div_eq_of_eq_mul_right h_pos this]

/- ACTUAL PROOF OF Nat.pow_div -/

example {x m n : Nat} (h : n ≤ m) (hx : 0 < x) : x ^ m / x ^ n = x ^ (m - n) := by
  rw [Nat.div_eq_iff_eq_mul_left (Nat.pow_pos hx) (Nat.pow_dvd_pow _ h), Nat.pow_sub_mul_pow _ h]