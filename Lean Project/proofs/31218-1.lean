import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  obtain ⟨d, hd⟩ := exists_eq_add_of_le h
  calc
    b + d = (a + b) + d - a := by rw [add_assoc, add_sub_cancel]
    ...   = a + c - a := by rw [hd]
    ...   = c := by rw [add_sub_cancel]

  exact le_iff_exists_add.2 ⟨d, rfl⟩

/- ACTUAL PROOF OF Nat.le_of_add_le_add_left -/

example {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply Nat.add_left_cancel hd