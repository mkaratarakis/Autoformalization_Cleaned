import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  intro h
  rw [add_comm a b, add_comm c b] at h
  exact Nat.le_of_add_le_add_right h

/- ACTUAL PROOF OF Nat.le_of_add_le_add_right -/

example {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  rw [Nat.add_comm _ b, Nat.add_comm _ b]
  apply Nat.le_of_add_le_add_left