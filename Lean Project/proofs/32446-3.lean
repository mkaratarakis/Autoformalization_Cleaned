import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  constructor
  · intro h
    apply And.intro
    · exact mt (mul_eq_zero_of_eq_zero_left h.symm)
    · exact mt (mul_eq_zero_of_eq_zero_right h.symm)
  · rintro ⟨hn, hm⟩
    exact mt mul_eq_zero_iff.mp (And.intro hn hm)

/- ACTUAL PROOF OF Nat.mul_ne_zero_iff -/

example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  rw [ne_eq, mul_eq_zero, not_or]