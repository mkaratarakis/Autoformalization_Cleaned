import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  have hk: ∃ k, n + k = m := exists_eq_add_of_le h
  cases' hk with k hk
  rw [← hk]
  simp [Nat.add_sub_cancel_left]

/- ACTUAL PROOF OF Nat.succ_sub -/

example {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]