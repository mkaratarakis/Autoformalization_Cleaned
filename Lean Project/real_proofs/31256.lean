import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m : Nat) : pred n * m = n * m - m := by
  cases n with
  | zero   => simp
  | succ n => rw [Nat.pred_succ, succ_mul, Nat.add_sub_cancel]