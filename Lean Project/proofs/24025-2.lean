import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat

example (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  intro h
  have h1 : gcd m n * lcm m n = m * n := gcd_mul_lcm m n
  rw [h] at h1
  simp at h1
  have h2 : m * n = 0 := h1
  have : m = 0 := by
    by_cases hn' : n = 0
    . exact hn hn'
    . exact Nat.eq_zero_of_mul_eq_zero h2 hn'
  contradiction

/- ACTUAL PROOF OF Nat.lcm_ne_zero -/

example (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  intro h
  have h1 := gcd_mul_lcm m n
  rw [h, Nat.mul_zero] at h1
  match mul_eq_zero.1 h1.symm with
  | .inl hm1 => exact hm hm1
  | .inr hn1 => exact hn hn1