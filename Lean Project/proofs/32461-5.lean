import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  unfold HMul.hMul HSub.hSub HAdd.hAdd
  repeat rw [add_mul, mul_add, mul_sub]
  apply Nat.sub_eq_of_eq_add
  rw [mul_comm, add_comm]

/- ACTUAL PROOF OF Nat.mul_self_sub_mul_self_eq -/

example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a,
    Nat.sub_add_eq, Nat.add_sub_cancel]