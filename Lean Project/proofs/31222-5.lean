import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero =>
    simp
    rfl
  | succ k ih =>
    calc
      (succ n) - (succ (succ k)) = succ (n - (succ k)) := rfl
      _ = n - k := ih

/- ACTUAL PROOF OF Nat.succ_sub_succ_eq_sub -/

example (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih