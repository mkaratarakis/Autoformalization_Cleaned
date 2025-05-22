import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (a b c : Nat) : min (a * c) (b * c) = min a b * c := by
  induction a generalizing b with
  | zero => simp
  | succ i ind =>
    cases b <;> simp [succ_eq_add_one, Nat.succ_mul, Nat.add_min_add_right, ind]