import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {m k : Nat} (h : k ≤ m) (n : Nat) : n + m - k = n + (m - k) := by
 cases Nat.le.dest h
 rename_i l hl
 rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]