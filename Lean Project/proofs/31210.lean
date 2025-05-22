import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a : Nat} (h : a ≠ 0) : 0 < a := by
  cases a with
  | zero =>
    apply False.elim
    exact h rfl
  | succ a' =>
    exact zero_lt_succ a'

/- ACTUAL PROOF OF Nat.zero_lt_of_ne_zero -/

example {a : Nat} (h : a ≠ 0) : 0 < a := by
  match a with
  | 0 => contradiction
  | a+1 => apply Nat.zero_lt_succ