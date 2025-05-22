import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  exact Nat.le_of_add_le_add_right h

/- ACTUAL PROOF OF Nat.le_of_add_le_add_left -/

example {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c := by
  match le.dest h with
  | ⟨d, hd⟩ =>
    apply @le.intro _ _ d
    rw [Nat.add_assoc] at hd
    apply Nat.add_left_cancel hd