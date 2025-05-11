import Init.Omega
example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  rw [← Nat.div_mod]
  rw [Nat.mod_mod_of_mul_div]
  rw [Nat.div_self]
  rw [Nat.mod_eq_of_lt]

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]