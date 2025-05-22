import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example {a b c : Nat} : a + b ≤ c + b → a ≤ c := by
  rw [Nat.add_comm _ b, Nat.add_comm _ b]
  apply Nat.le_of_add_le_add_left