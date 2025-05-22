import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



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