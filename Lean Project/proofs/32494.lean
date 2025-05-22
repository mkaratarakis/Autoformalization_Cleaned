import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m x y : Nat) : (m * x + y) % m = y % m := by
  induction x with
  | zero =>
    simp
  | succ x' ih =>
    rw [Nat.mul_succ, Nat.add_assoc]
    simp [Nat.mod_eq_of_lt]
    rw [ih]

/- ACTUAL PROOF OF Nat.mul_add_mod -/

example (m x y : Nat) : (m * x + y) % m = y % m := by
  match x with
  | 0 => simp
  | x + 1 =>
    simp [Nat.mul_succ, Nat.add_assoc _ m, mul_add_mod _ x]