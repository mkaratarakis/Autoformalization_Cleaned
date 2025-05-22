import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  have h' : b - d + d = b := by
    apply Nat.sub_add_cancel
    exact h
  constructor
  . intro h1
    calc
      a + (b - d) = a + (b - d + d - d) := by rw [h', Nat.sub_sub_self]
      _ = a + b - d := by rw [Nat.add_sub_assoc]
      _ = c := by rw [h1, Nat.sub_sub_self]
  . intro h2
    calc
      a + b = a + (b - d + d) := by rw [h']
      _ = a + (b - d) + d := by rw [add_assoc]
      _ = c + d := by rw [h2]

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_ge -/

example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  rw [@Eq.comm _ (a + b) _, add_eq_add_le c a h, @Eq.comm _ _ c]