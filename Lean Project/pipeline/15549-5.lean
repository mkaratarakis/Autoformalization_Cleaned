import Init.Omega
example (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ b k]
  rw [Nat.mod_eq_of_lt (Nat.mod_lt x (b^k * b))]

/- ACTUAL PROOF OF Nat.mod_pow_succ -/

example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ, Nat.mod_mul]