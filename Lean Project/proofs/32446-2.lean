import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  constructor
  · intro h
    cases h.lt_or_lt with
    | inl hn => exact ⟨hn.ne', hn.ne'.elim⟩
    | inr hm => exact ⟨hm.ne'.elim, hm.ne'⟩
  · rintro ⟨hn, hm⟩
    exact (mul_ne_zero hn hm)

/- ACTUAL PROOF OF Nat.mul_ne_zero_iff -/

example : n * m ≠ 0 ↔ n ≠ 0 ∧ m ≠ 0 := by
  rw [ne_eq, mul_eq_zero, not_or]