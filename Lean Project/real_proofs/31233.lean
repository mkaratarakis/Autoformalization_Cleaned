import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (a i : Nat) (h : i < a) : a - (i + 1) < a - i := by
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption