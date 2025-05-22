import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n : Nat) : 1 ^ n = 1 := by
  induction n with
  | zero =>
    -- Base case: 1^0 = 1
    rfl
  | succ k ih =>
    -- Inductive step: Assume 1^k = 1, show 1^(k+1) = 1
    simp [Nat.pow_succ, ih, one_mul]

/- ACTUAL PROOF OF Nat.one_pow -/

example (n : Nat) : 1 ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ _ ih => rw [Nat.pow_succ, Nat.mul_one, ih]