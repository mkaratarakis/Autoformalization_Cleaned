import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m : Nat) : succ n - succ m = n - m := by
  induction m with
  | zero      => exact rfl
  | succ m ih => apply congrArg pred ih