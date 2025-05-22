import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n : Nat} (H : 0 < n) : 0 ^ n = 0 := by
  cases n with
  | zero =>
    -- In this case, n = 0, which contradicts the hypothesis 0 < n.
    exfalso
    exact H
  | succ k =>
    -- In this case, n = k + 1.
    rw [pow_succ]
    -- Now we have 0 ^ (k + 1) = 0 ^ k * 0.
    rw [zero_mul]
    -- Since 0 * 0 = 0, we have 0 ^ (k + 1) = 0.
    exact zero_pow (Nat.succ_pos _)

/- ACTUAL PROOF OF Nat.zero_pow -/

example {n : Nat} (H : 0 < n) : 0 ^ n = 0 := by
  match n with
  | 0 => contradiction
  | n+1 => rw [Nat.pow_succ, Nat.mul_zero]