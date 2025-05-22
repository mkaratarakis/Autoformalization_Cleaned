import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]