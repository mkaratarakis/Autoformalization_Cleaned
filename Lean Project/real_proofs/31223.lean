import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a : Nat} (h : a ≠ 0) : a - 1 + 1 = a := by
  induction a with
  | zero => contradiction
  | succ => rfl