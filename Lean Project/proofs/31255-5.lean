import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a < c - b) : a + b < c := by
  have hle : b ≤ c := by
    push_neg at h
    exact le_of_not_lt h
  have hle' : a + b ≤ c := by
    apply add_le_add_left
    apply le_of_lt
    exact h
  exact lt_of_le_of_lt hle' (lt_add_one_iff.mpr h)

/- ACTUAL PROOF OF Nat.add_lt_of_lt_sub -/

example {a b c : Nat} (h : a < c - b) : a + b < c := by
  have hle : b ≤ c := by
    apply Nat.ge_of_not_lt
    intro hgt
    apply Nat.not_lt_zero a
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)] at h
    exact h
  have : a.succ + b ≤ c := add_le_of_le_sub hle h
  simp [Nat.succ_add] at this
  exact this