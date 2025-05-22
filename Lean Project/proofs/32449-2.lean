import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  intro h'
  apply Nat.lt_irrefl
  apply Nat.mul_eq_zero_iff.mp
  apply Nat.eq_zero_of_le_zero
  apply Nat.not_le_of_lt
  assumption

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_right -/

example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all