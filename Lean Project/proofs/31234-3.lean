import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.sub_eq_iff_eq_add]
  constructor
  · intro h1
    exact Nat.add_comm c b ▸ h1
  · intro h1
    exact Nat.add_comm c b ▸ h1

/- ACTUAL PROOF OF Nat.sub_eq_iff_eq_add' -/

example {c : Nat} (h : b ≤ a) : a - b = c ↔ a = b + c := by
  rw [Nat.add_comm, Nat.sub_eq_iff_eq_add h]