import Init.Omega
example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  rw [Nat.mod_mul_left_div_self]

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]