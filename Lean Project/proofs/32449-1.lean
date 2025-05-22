import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  by_contra h'
  have : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h')
  rw [this] at h
  apply Nat.not_lt_zero
  exact h

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_right -/

example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all