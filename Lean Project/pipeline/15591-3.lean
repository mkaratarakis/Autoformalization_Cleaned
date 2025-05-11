import Init.Omega
example (m n k : Nat) : m % (n * k) / n = m / n % k := by
  by_cases hn : n = 0
  · -- Case 1: n = 0
    -- Both sides are undefined, so the goal is trivially true
    simp [hn]
  · have hk : k = 0 ∨ k = Nat.succ _ := by
      by_cases hk' : k = 0
      · exact Or.inl hk'
      · exact Or.inr (Nat.succ.inj (Ne.symm (Ne.of_not_eq hk')))
    cases hk with
    | inl hk =>
      -- Case 2.1: k = 0
      -- Both sides are undefined, so the goal is trivially true
      simp [hk]
    | inr hk =>
      -- Case 2.2: k > 0
      have h1 : m % (n * k) + (n * k) * (m / (n * k)) = m := Nat.mod_add_div m (n * k)
      rw [h1]
      have h2 : (n * k) * (m / (n * k)) = n * (k * (m / (n * k))) := by simp [Nat.mul_assoc]
      rw [h2]
      rw [← Nat.div_add_mod (m % (n * k)) (Nat.succ.inj (Ne.symm (Ne.of_not_eq hn)))]
      simp
      rw [Nat.mod_eq_of_lt]
      apply Nat.mod_lt
      exact Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero (Ne.symm (Ne.of_not_eq hk)))

/- ACTUAL PROOF OF Nat.mod_mul_right_div_self -/

example (m n k : Nat) : m % (n * k) / n = m / n % k := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn); simp [mod_zero]
  rcases Nat.eq_zero_or_pos k with (rfl | hk); simp [mod_zero]
  conv => rhs; rw [← mod_add_div m (n * k)]
  rw [Nat.mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (Nat.mul_pos hn hk)))]