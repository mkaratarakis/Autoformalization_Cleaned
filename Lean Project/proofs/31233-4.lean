import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.sub_succ]
  apply Nat.pred_lt
  exact Nat.sub_pos_of_lt h

/- ACTUAL PROOF OF Nat.sub_succ_lt_self -/

example (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption