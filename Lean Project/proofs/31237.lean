import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero =>
    rfl
  | succ m' ih =>
    simp [Nat.succ_mul, ih]
    rw [Nat.add_comm (n * m'), Nat.add_assoc]

/- ACTUAL PROOF OF Nat.succ_mul -/

example (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]