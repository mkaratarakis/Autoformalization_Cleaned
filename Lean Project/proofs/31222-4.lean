import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero =>
    simp
    rfl
  | succ k ih =>
    simp
    exact Nat.succ_pred_eq_of_pos (succ_ne_zero _)

/- ACTUAL PROOF OF Nat.succ_sub_succ_eq_sub -/

example (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih