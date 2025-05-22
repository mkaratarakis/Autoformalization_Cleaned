import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  obtain hd : a + b + d = c := exists_eq_add_of_le h
  rw [add_comm b d, ← add_assoc] at hd
  rw [hd]
  obtain rfl := Nat.add_sub_cancel c b
  exact Nat.le_sub_left_of_add_le h

/- ACTUAL PROOF OF Nat.le_sub_of_add_le -/

example {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    have hd : a + d + b = c := by simp [← hd, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
    have hd := Nat.sub_eq_of_eq_add hd.symm
    exact hd.symm