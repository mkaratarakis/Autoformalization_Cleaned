import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [add_assoc]
  rw [add_comm m k]
  rw [←add_assoc]

/- ACTUAL PROOF OF Nat.add_right_comm -/

example (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]