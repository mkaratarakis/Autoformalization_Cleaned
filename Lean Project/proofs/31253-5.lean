import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    rw [Nat.sub_succ]
    rw [Nat.mul_succ, ih, Nat.sub_sub, Nat.mul_succ, Nat.add_sub_cancel_left]
    simp

/- ACTUAL PROOF OF Nat.mul_sub_right_distrib -/

example (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.sub_succ, Nat.pred_mul, ih, succ_mul, Nat.sub_sub]; done