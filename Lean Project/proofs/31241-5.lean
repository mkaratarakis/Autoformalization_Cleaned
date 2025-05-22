import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let k := m - n
  have hk : m = n + k := (Nat.add_sub_of_le h).symm
  rw [hk]
  simp

/- ACTUAL PROOF OF Nat.succ_sub -/

example {m n : Nat} (h : n ≤ m) : succ m - n = succ (m - n) := by
  let ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]