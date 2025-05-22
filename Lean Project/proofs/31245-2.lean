import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat

example {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have h1 := Nat.le_sub_left_of_add_le h
  exact Nat.lt_of_le_of_lt h1 H

/- ACTUAL PROOF OF Nat.sub_lt_left_of_lt_add -/

example {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this