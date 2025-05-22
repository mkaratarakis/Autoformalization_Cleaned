import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b ≤ c + d) = (a ≤ c + (d - b)) := by
  apply Iff.intro
  · intro h1
    calc
      a ≤ c + d - b := by
        rw [Nat.sub_add_cancel h]
        exact h1

  · intro h2
    rw [← Nat.sub_add_cancel h]
    exact h2

/- ACTUAL PROOF OF Nat.Simproc.add_le_add_le -/

example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b ≤ c + d) = (a ≤ c + (d - b)) := by
  rw [← Nat.add_sub_assoc h, Nat.le_sub_iff_add_le]
  exact Nat.le_trans h (le_add_left d c)