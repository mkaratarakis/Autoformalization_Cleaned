import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  by_contra hb
  push_neg at hb
  cases b
  · simp at h
  exact Nat.not_lt_zero _ h

/- ACTUAL PROOF OF Nat.pos_of_mul_pos_left -/

example {a b : Nat} (h : 0 < a * b) : 0 < b := by
  apply Decidable.by_contra
  intros
  simp_all