import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc



example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (le_add_left d c)
  rw [← Nat.add_sub_assoc h, @Eq.comm _ a, Nat.sub_eq_iff_eq_add g, @Eq.comm _ (a + b)]