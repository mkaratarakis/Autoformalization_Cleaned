import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m : Nat) : n - m ≤ n := by
  induction m with
  | zero      => exact Nat.le_refl (n - 0)
  | succ m ih => apply Nat.le_trans (pred_le (n - m)) ih