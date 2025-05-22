import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {n m k : Nat} (hm : 0 < m) (h : n * m = k * m) : n = k := by
  exact Nat.mul_right_cancel hm h

/- ACTUAL PROOF OF Nat.eq_of_mul_eq_mul_right -/

example {n m k : Nat} (hm : 0 < m) (h : n * m = k * m) : n = k := by
  rw [Nat.mul_comm n m, Nat.mul_comm k m] at h; exact Nat.eq_of_mul_eq_mul_left hm h