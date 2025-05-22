import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (n : Nat) : 1 ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.pow_succ, Nat.mul_one, ih]