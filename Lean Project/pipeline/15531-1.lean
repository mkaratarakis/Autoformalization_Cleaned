import Init.Omega
example (h : b * a < c * a) : b < c := by
  have h₁ : a * b < a * c := by
    convert h
    rw [Nat.mul_comm a b, Nat.mul_comm a c]
  exact Nat.lt_of_mul_lt_mul_left h₁

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_right -/

example {a b c : Nat} (h : b * a < c * a) : b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a] at h
  exact Nat.lt_of_mul_lt_mul_left h