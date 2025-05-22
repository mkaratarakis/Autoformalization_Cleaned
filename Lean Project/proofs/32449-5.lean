import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  by_contra h'
  replace h' : a = 0
  · apply le_zero_iff.mp
    apply Nat.not_lt
    exact h'
  rw [h'] at h
  exact absurd h (not_lt_zero 0)

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_right -/

example {a b : Nat} (h : 0 < a * b) : 0 < a := by
  apply Decidable.by_contra
  intros
  simp_all