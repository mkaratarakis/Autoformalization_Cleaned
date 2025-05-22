import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n : Nat) : n = n - 1 ↔ n = 0 := by
  cases n <;> simp [add_one_ne]