import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m k : Nat) : n * m * k = n * k * m := by
  calc
    n * m * k = n * (m * k) := Nat.mul_assoc n m k
            _ = n * (k * m) := congrArg ((·) * ·) (Nat.mul_comm m k)
            _ = n * k * m := Nat.mul_assoc n k m

/- ACTUAL PROOF OF Nat.mul_right_comm -/

example (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]