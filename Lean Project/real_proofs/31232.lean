import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (a i : Nat) : a - i ≤ a.succ - i := by
  cases i with
  | zero => apply Nat.le_of_lt; apply Nat.lt_succ_self
  | succ i => rw [Nat.sub_succ, Nat.succ_sub_succ]; apply Nat.pred_le