import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  rw [← Ne.def, ← Ne.def, ← Ne.def]
  rw [mul_eq_zero_iff]
  rw [not_or]

/- ACTUAL PROOF OF Nat.mul_ne_zero_iff -/

example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  rw [ne_eq, mul_eq_zero, not_or]