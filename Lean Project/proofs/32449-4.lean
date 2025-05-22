import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  by_contra h'
  have h₁ : a = 0 := by
    by_contra h''
    apply h'
    exact mul_pos h'' (pos_of_ne_zero (Ne.symm (Ne.of_lt h)))
  rw [h₁] at h
  exact Nat.not_lt_zero 0 h

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_right -/

example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all