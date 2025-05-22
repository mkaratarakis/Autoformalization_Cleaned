import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
  have hl : ∃ l, k + l = m
  exact Nat.le_iff_exists_add.mp h
  obtain ⟨l, hl⟩ := hl
  rw [hl]
  rw [add_assoc n k l]
  rw [add_sub_cancel]
  rfl

/- ACTUAL PROOF OF Nat.add_sub_assoc -/

example {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 cases Nat.le.dest h
 rename_i l hl
 rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]