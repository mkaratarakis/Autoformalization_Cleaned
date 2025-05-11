import Init.Omega
example (m n k : Nat) : m % (n * k) / n = m / n % k := by
  cases n with
  | zero =>
    -- Case 1: n = 0
    -- Both sides are undefined, so the goal is trivially true
    simp
  | succ n' =>
    cases k with
    | zero =>
      -- Case 2.1: k = 0
      -- Both sides are undefined, so the goal is trivially true
      simp
    | succ k' =>
      -- Case 2.2: k > 0
      have h1 : m % (n * k) + (n * k) * (m / (n * k)) = m := Nat.mod_add_div m (n * k)
      rw [h1]
      simp [Nat.mul_assoc, Nat.div_add_mod]
      rw [Nat.add_div_assoc]
      rw [Nat.mod_eq_of_lt]
      apply Nat.mod_lt
      exact Nat.mul_pos n' k'

/- ACTUAL PROOF OF Nat.mod_mul_right_div_self -/

example (m n k : Nat) : m % (n * k) / n = m / n % k := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn); simp [mod_zero]
  rcases Nat.eq_zero_or_pos k with (rfl | hk); simp [mod_zero]
  conv => rhs; rw [← mod_add_div m (n * k)]
  rw [Nat.mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (Nat.mul_pos hn hk)))]