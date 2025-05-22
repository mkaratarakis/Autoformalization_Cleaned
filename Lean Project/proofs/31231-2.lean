import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero =>
    simp
  | succ a ih =>
    rw [add_succ, add_succ, Nat.sub_succ, ih]

/- ACTUAL PROOF OF Nat.add_sub_self_left -/

example (a b : Nat) : (a + b) - a = b := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, Nat.succ_sub_succ]
    apply ih