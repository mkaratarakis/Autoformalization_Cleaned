import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (Nat.le_add_right d c)
  calc
    (a + b = c + d) = (c + d = a + b) := propext Eq.symm
    _ = (c + d - b = a) := by rw [Nat.eq_iff_eq_of_le g]
    _ = (a = c + d - b) := propext Eq.symm

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_le -/

example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (le_add_left d c)
  rw [← Nat.add_sub_assoc h, @Eq.comm _ a, Nat.sub_eq_iff_eq_add g, @Eq.comm _ (a + b)]