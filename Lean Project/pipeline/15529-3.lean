import Init.Omega
example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  have h1 : m % (n * k) < n * k := Nat.mod_lt _ (Nat.zero_lt_mul_right _ _)
  have h2 : m % (n * k) / n < k := Nat.div_lt_of_lt_mul h1
  rw [Nat.div_eq_of_lt h2]
  rw [Nat.mod_eq_of_lt]
  rw [Nat.div_eq_of_lt]

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]