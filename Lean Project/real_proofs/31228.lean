import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n : Nat) : n - 1 = n ↔ n = 0 := by
  cases n <;> simp [ne_add_one]