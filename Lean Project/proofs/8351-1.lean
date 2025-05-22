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
  calc
    a + b = a + (b - d + d) := by rw [h']
    _ = (a + (b - d)) + d := by rw [add_assoc]
    _ = c + d := by rw [← add_right_inj]

  exact Iff.intro (fun h => by rw [h]) (fun h => by rw [← h])

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_ge -/

example (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  rw [@Eq.comm _ (a + b) _, add_eq_add_le c a h, @Eq.comm _ _ c]