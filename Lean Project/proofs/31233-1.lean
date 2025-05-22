import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.sub_succ]
  exact Nat.pred_lt (Nat.sub_lt (Nat.lt_of_succ_lt_succ h ))

/- ACTUAL PROOF OF Nat.sub_succ_lt_self -/

example (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption