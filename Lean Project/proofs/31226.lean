import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n : Nat) : n = n - 1 ↔ n = 0 := by
  cases n with
  | zero =>
    simp [Nat.pred]
  | succ d =>
    simp [Nat.pred, Nat.add, Nat.one_add]

/- ACTUAL PROOF OF Nat.eq_self_sub_one -/

example (n : Nat) : n = n - 1 ↔ n = 0 := by
  cases n <;> simp [add_one_ne]