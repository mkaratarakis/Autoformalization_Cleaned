import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (Nat.le_add_right c d)
  calc
    (a + b = c + d) = (c + d = a + b) := propext (Iff.intro Eq.symm Eq.symm)
    _ = (c + d - b = a) := by rw [Nat.sub_eq_iff_eq_add g]
    _ = (a = c + d - b) := propext (Iff.intro Eq.symm Eq.symm)
    _ = (a = c + (d - b)) := by simp only [add_sub_assoc]

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_le -/

example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (le_add_left d c)
  rw [← Nat.add_sub_assoc h, @Eq.comm _ a, Nat.sub_eq_iff_eq_add g, @Eq.comm _ (a + b)]