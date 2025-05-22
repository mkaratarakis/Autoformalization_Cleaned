import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
  induction' b with b hb
  · -- Base case: b = 0
    simp [zero_mul, max_zero_left]
  · -- Inductive step: b = n + 1
    rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
    rw [max_add_add_left]
    rw [hb]

/- ACTUAL PROOF OF Nat.mul_max_mul_right -/

example (a b c : Nat) : max (a * c) (b * c) = max a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_max_add_right, ind]