import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero =>
    rfl
  | succ m' ih =>
    show succ (succ n * m' + n) = succ n * m' + n + succ m'
    rw [Nat.succ_add, Nat.add_succ]
    exact ih

/- ACTUAL PROOF OF Nat.succ_mul -/

example (n m : Nat) : (succ n) * m = (n * m) + m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [mul_succ, add_succ, ih, mul_succ, add_succ, Nat.add_right_comm]