import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [mul_sub_right_distrib, mul_add]
  rw [← add_mul, ← add_mul]
  rw [add_comm (b * a), add_comm (a * b)]
  rw [sub_eq_add_neg, add_comm (a * b), add_comm (b * b)]
  rw [add_assoc, add_assoc, ← add_assoc (a * a), ← add_assoc (a * a)]
  rw [add_left_cancel, add_left_cancel, add_left_cancel]
  rfl

/- ACTUAL PROOF OF Nat.mul_self_sub_mul_self_eq -/

example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a,
    Nat.sub_add_eq, Nat.add_sub_cancel]