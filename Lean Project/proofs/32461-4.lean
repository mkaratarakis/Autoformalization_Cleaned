import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [← mul_add (a + b) a (a - b), ← mul_add (a + b) b (a - b),
      add_comm (b * a) (a * a), add_comm (a * b) (b * b),
      add_sub_cancel, add_sub_cancel]
  rfl

/- ACTUAL PROOF OF Nat.mul_self_sub_mul_self_eq -/

example (a b : Nat) : a * a - b * b = (a + b) * (a - b) := by
  rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a,
    Nat.sub_add_eq, Nat.add_sub_cancel]