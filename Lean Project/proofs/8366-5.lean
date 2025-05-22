import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b ≤ c + d) = (a + (b - d) ≤ c) := by
  apply Propext
  constructor
  . intro h1
    rwa [Nat.add_sub_assoc]
    apply Nat.le_sub_right_iff h
    exact h1
  . intro h1
    rwa [←Nat.add_sub_assoc]
    apply Nat.le_sub_right_iff h
    exact h1

/- ACTUAL PROOF OF Nat.Simproc.add_le_add_ge -/

example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b ≤ c + d) = (a + (b - d) ≤ c) := by
  rw [← Nat.add_sub_assoc h, Nat.sub_le_iff_le_add]