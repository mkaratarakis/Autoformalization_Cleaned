import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat

example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  constructor
  · intro h1
    rw [Nat.sub_eq_iff_eq_add h] at h1
    exact h1
  · intro h1
    rw [←Nat.sub_eq_iff_eq_add h]
    exact h1

/- ACTUAL PROOF OF Nat.sub_eq_iff_eq_add' -/

example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]