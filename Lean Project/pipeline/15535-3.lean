import Init.Omega
example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a using Nat.recOn
  case zero =>
    simp
    exact fun h => False.elim (Nat.not_lt_zero _ h)
  case succ a ih =>
    simp [Nat.succ_mul]
    constructor
    · intro h
      apply Nat.lt_of_add_lt_add_left
      apply (ih (Nat.zero_lt_succ _))
      simpa using h
    · intro h
      apply (ih (Nat.zero_lt_succ _)).2
      simpa [h]

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega