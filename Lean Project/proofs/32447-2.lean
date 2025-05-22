import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  intro hb
  apply False.elim
  apply h
  rw [mul_eq_zero_iff]
  left
  exact hb

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_left -/

example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  apply Decidable.by_contra
  intros
  simp_all