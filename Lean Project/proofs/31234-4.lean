import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat

example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  constructor
  · intro h1
    rw [Nat.sub_eq_iff_eq_add (le_of_sub_eq h1)]
    exact Nat.add_comm c b
  · intro h1
    rw [add_comm] at h1
    exact Nat.sub_eq_iff_eq_add.mpr h1

/- ACTUAL PROOF OF Nat.sub_eq_iff_eq_add' -/

example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]