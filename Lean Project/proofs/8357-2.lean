import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a : Nat) {b c : Nat} (h : b ≤ c) : (a + b ≤ c) = (a ≤ c - b) := by
  have intermediate_result: a + b ≤ 0 + c ↔ a ≤ 0 + (c - b) := by
    rw [add_comm]
    simp
  rw [zero_add] at intermediate_result
  exact intermediate_result

/- ACTUAL PROOF OF Nat.Simproc.add_le_le -/

example (a : Nat) {b c : Nat} (h : b ≤ c) : (a + b ≤ c) = (a ≤ c - b) := by
  have r := add_le_add_le a 0 h
  simp only [Nat.zero_add] at r
  exact r