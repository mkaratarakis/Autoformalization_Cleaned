import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m k n : Nat) : k * m ≤ m + n ↔ (k-1) * m ≤ n := by
  induction k with
  | zero =>
    simp
  | succ k' _ =>
    simp [mul_succ, add_comm, add_le_add_iff_right]
    exact ih

/- ACTUAL PROOF OF Nat.mul_le_add_right -/

example (m k n : Nat) : k * m ≤ m + n ↔ (k-1) * m ≤ n := by
  match k with
  | 0 =>
    simp
  | succ k =>
    simp [succ_mul, Nat.add_comm _ m, Nat.add_le_add_iff_left]