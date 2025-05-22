import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n m k : Nat} (mp : 0 < m) (h : n * m = k * m) : n = k := by
have h1 : m * n = m * k := by
  rw [mul_comm n m]
  rw [mul_comm k m]
  exact h
exact Nat.mul_right_cancel h1 mp

/- ACTUAL PROOF OF Nat.mul_right_cancel -/

example {n m k : Nat} (mp : 0 < m) (h : n * m = k * m) : n = k := by
  simp [Nat.mul_comm _ m] at h
  apply Nat.mul_left_cancel mp h