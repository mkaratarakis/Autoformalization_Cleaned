import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (hle : b ≤ c) (h : a ≤ c - b) : a + b ≤ c := by
  cases hle
  case refl =>
      simp only [sub_self, add_zero] at h
      exact h
  case step c hle =>
      simp only [sub_succ, Nat.succ_le_succ_iff] at h
      apply Nat.le_succ_of_le
      apply Nat.le_add_left
      exact h

/- ACTUAL PROOF OF Nat.add_le_of_le_sub -/

example {a b c : Nat} (hle : b ≤ c) (h : a ≤ c - b) : a + b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.eq_add_of_sub_eq hle hd.symm]
    simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]