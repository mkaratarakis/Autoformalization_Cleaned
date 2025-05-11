import Init.Omega
example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  have h : m = n * (m / n) + m % n := Nat.div_add_mod m n
  rw [h]
  rw [Nat.mul_comm]
  rw [Nat.div_mul_right]
  rw [Nat.div_div]
  rw [Nat.div_self]
  rw [Nat.mod_eq_of_lt]
  exact h

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]