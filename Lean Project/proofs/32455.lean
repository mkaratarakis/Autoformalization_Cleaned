import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n m k : Nat} (np : 0 < n) (h : n * m = n * k) : m = k := by
  apply Nat.eq_of_mul_eq_mul_left np h

/- ACTUAL PROOF OF Nat.mul_left_cancel -/

example {n m k : Nat} (np : 0 < n) (h : n * m = n * k) : m = k := by
  match Nat.lt_trichotomy m k with
  | Or.inl p =>
    have r : n * m < n * k := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r
  | Or.inr (Or.inl p) => exact p
  | Or.inr (Or.inr p) =>
    have r : n * k < n * m := Nat.mul_lt_mul_of_pos_left p np
    simp [h] at r