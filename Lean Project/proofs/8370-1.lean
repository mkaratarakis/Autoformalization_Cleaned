import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (Nat.le_add_right _ _)
  calc
    (a + b = c + d) = (c + d = a + b) := propext Eq.symm
    _ = (c + d - b = a) := by rw [Nat.eq_iff_eq_of_le g]
    _ = (a = c + d - b) := propext Eq.symm
example {a b c : Nat} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  exact Nat.le_trans h₁ h₂

theorem Nat.le_add_right (a b : Nat) : a ≤ a + b := by
  exact Nat.le_add_right a b

theorem propext {p q : Prop} (h : p ↔ q) : p = q := by
  exact propext h

/- ACTUAL PROOF OF Nat.Simproc.add_eq_add_le -/

example (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (le_add_left d c)
  rw [← Nat.add_sub_assoc h, @Eq.comm _ a, Nat.sub_eq_iff_eq_add g, @Eq.comm _ (a + b)]