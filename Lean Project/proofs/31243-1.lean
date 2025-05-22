import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
  have hl : ∃ l : Nat, k + l = m
  exact Nat.le_iff_exists_add.mp h
  cases' hl with l hl
  rw [hl]
  rw [add_assoc]
  rw [add_sub_cancel]
  rw [←add_assoc]
  rw [add_sub_cancel]
  rfl

/- ACTUAL PROOF OF Nat.add_sub_assoc -/

example {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 cases Nat.le.dest h
 rename_i l hl
 rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]