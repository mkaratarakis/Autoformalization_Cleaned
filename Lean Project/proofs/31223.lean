import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a : Nat} (h : a ≠ 0) : a - 1 + 1 = a := by
cases a with
  | zero =>
    contradiction
  | succ n =>
    simp

/- ACTUAL PROOF OF Nat.sub_one_add_one -/

example {a : Nat} (h : a ≠ 0) : a - 1 + 1 = a := by
  induction a with
  | zero => contradiction
  | succ => rfl