import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n) : 2 * n = n + n := by
  rw [Nat.succ_mul, Nat.one_mul]