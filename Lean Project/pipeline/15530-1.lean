import Init.Omega
example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [mul_comm b a, mul_comm c a]
  exact Nat.mul_lt_mul_left a0

/- ACTUAL PROOF OF Nat.mul_lt_mul_right -/

example (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_lt_mul_left a0]