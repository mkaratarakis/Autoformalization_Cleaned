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
  apply Iff.intro
  · intro h1
    rw [h', add_assoc, h1, Nat.add_sub_cancel_right]
  · intro h2
    rw [←h', add_assoc, h2, Nat.add_sub_cancel_right]

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_ge -/

example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  rw [@Eq.comm _ (a + b) _, add_eq_add_le c a h, @Eq.comm _ _ c]