import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m k : Nat) : (n - m) * k = n * k - m * k := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.sub_succ, Nat.pred_mul, ih, succ_mul, Nat.sub_sub]; done