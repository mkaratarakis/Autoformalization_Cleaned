import Init.Omega
example (h : b * a < c * a) : b < c := by
  have h₁ : a * b < a * c := by
    rwa [Nat.mul_comm]
  exact Nat.lt_of_mul_lt_mul_left h₁ (Nat.zero_le a)

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_right -/

example {a b c : Nat} (h : b * a < c * a) : b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a] at h
  exact Nat.lt_of_mul_lt_mul_left h