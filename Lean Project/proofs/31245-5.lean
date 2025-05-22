import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat

example {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have h1 : k + 1 ≤ n + m := Nat.succ_le_of_lt h
  have h2 : (k + 1) - n ≤ (n + m) - n := Nat.sub_le_sub_right h1 n
  simp at h2
  rw [Nat.succ_sub H, Nat.sub_self] at h2
  exact Nat.lt_of_succ_le h2

/- ACTUAL PROOF OF Nat.sub_lt_left_of_lt_add -/

example {n k m : Nat} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this