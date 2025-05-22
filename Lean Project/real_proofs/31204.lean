import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m k : Nat) : (n + m) + k = (n + k) + m := by
  rw [Nat.add_assoc, Nat.add_comm m k, ← Nat.add_assoc]